import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4478`: `x ◇ (y ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4478 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4478 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4478.models_iff G M).mp hM
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
      · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
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
        have b0e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e16 X1 (τ X0)
             have i₂ := b0e13 X0
             grind)
          | exact superpose b0e13 b0e16
          | exact resolve b0e16 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e31 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op (M.op (M.op X0 X0) X1) X2)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b0e11 X3 (M.op X0 X0) X4 X5
             have i₂ := b0e11 (M.op X0 X0) X0 X1 X2
             grind)
          | exact superpose b0e11 b0e11
          | exact resolve b0e11 b0e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e11 X0 (σ y) X1 X2
             have i₂ := b0e19
             grind)
          | exact superpose b0e19 b0e11
          | exact resolve b0e11 b0e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x X1) := by
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
        have b0e40 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
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
        have b0e46 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op (M.op X0 X0) (σ y))) := by
          intro X0 X3 X4 X5
          first
          | (have i₁ := b0e31 X0 x x X3 X4 X5
             have i₂ := b0e33 (M.op X0 X0) x x
             grind)
          | exact superpose b0e33 b0e31
          | exact resolve b0e31 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31
        have b0e47 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X0 (σ y))) := by
          intro X0 X3 X4 X5
          first
          | (have i₁ := b0e46 X0 X3 X4 X5
             have i₂ := b0e33 X0 X0 (σ y)
             grind)
          | exact superpose b0e33 b0e46
          | exact resolve b0e46 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e48 : ∀ X0 X3 : G, (M.op X3 (M.op X0 (σ y))) = (M.op X3 (σ y)) := by
          intro X0 X3
          first
          | (have i₁ := b0e47 X0 X3 x x
             have i₂ := b0e33 X3 x x
             grind)
          | exact superpose b0e33 b0e47
          | exact resolve b0e47 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e54 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e39 x X2
             have i₂ := b0e39 x X0
             grind)
          | (have i₁ := b0e39 X0 x
             have i₂ := b0e39 X0 (M.op X0 X0)
             grind)
          | exact superpose b0e39 b0e39
          | exact resolve b0e39 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e74 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
        have b0e75 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) ∨ (k X3 (M.op X0 X0)) = (M.op X3 (M.op X0 X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e11 (M.op X0 X0) X0 X1 X2
             have i₂ := b0e15 X3 (M.op X0 X0)
             grind)
          | exact superpose b0e15 b0e11
          | (have j1 := b0e15 X3 (M.op X0 X0)
             grind)
          | exact resolve b0e11 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b0e82 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b0e74 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e74
        have b0e83 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) ∨ (k X3 (M.op X0 X0)) = (M.op X3 (M.op X0 X0)) := by
          intro X0 X3
          first
          | (have i₁ := b0e75 X0 x x X3
             have i₂ := b0e33 (M.op X0 X0) x x
             grind)
          | exact superpose b0e33 b0e75
          | (have j0 := b0e75 X0 x x X3
             grind)
          | exact resolve b0e75 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e75
        have b0e86 : ∀ X0 X3 : G, (k X3 (M.op X0 X0)) = (M.op X3 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0 X3
          first
          | (have i₁ := b0e83 X0 X3
             have i₂ := b0e33 X0 X0 (σ y)
             grind)
          | exact superpose b0e33 b0e83
          | (have j0 := b0e83 X0 X3
             grind)
          | exact resolve b0e83 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e83
        have b0e107 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e20
             have i₂ := b0e54 x X0
             grind)
          | (have i₁ := b0e20
             have i₂ := b0e54 X0 x
             grind)
          | exact superpose b0e54 b0e20
          | exact resolve b0e20 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54
        have b0e126 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b0e40 x X2
             have i₂ := b0e40 x X0
             grind)
          | (have i₁ := b0e40 X0 x
             have i₂ := b0e40 X0 (M.op X0 X0)
             grind)
          | exact superpose b0e40 b0e40
          | exact resolve b0e40 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e201 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e18
             have i₂ := b0e126 y X0
             grind)
          | (have i₁ := b0e18
             have i₂ := b0e126 X0 y
             grind)
          | exact superpose b0e126 b0e18
          | exact resolve b0e18 b0e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e126
        have b0e232 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e11 X0 X1 x x
             have i₂ := b0e33 X0 x x
             grind)
          | exact superpose b0e33 b0e11
          | exact resolve b0e11 b0e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33
        have b0e664 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e48 y X0
             have i₂ := b0e201 (σ y)
             grind)
          | exact superpose b0e201 b0e48
          | exact resolve b0e48 b0e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48 b0e201
        have b0e978 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b0e82 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e82
        have b0e1875 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e17
             have i₂ := b0e664 (σ x)
             grind)
          | exact superpose b0e664 b0e17
          | exact resolve b0e17 b0e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e1883 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b0e1875
             have i₂ := b0e107 y
             grind)
          | exact superpose b0e107 b0e1875
          | exact resolve b0e1875 b0e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e1875
        have b0e2904 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b0e81 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e81
        have b0e3970 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b0e978 x X0
             have i₂ := b0e107 X0
             grind)
          | exact superpose b0e107 b0e978
          | (have j0 := b0e978 x X0
             grind)
          | (have r₁ := b0e978 x X0
             have r₂ := b0e107 X0
             grind)
          | exact resolve b0e978 b0e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e107 b0e978
        have b0e3982 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b0e3970 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e3970
        have b0e4124 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b0e28 X0 x
             have i₂ := b0e3982 (τ X0)
             grind)
          | exact superpose b0e3982 b0e28
          | exact resolve b0e28 b0e3982
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e28
        have b0e4945 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e86 X0 (σ x)
             have i₂ := b0e4124 (M.op X0 X0)
             grind)
          | exact superpose b0e4124 b0e86
          | (have j0 := b0e86 X0 x
             grind)
          | exact resolve b0e86 b0e4124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e86 b0e4124
        have b0e4956 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e4945 X0
             have i₂ := b0e232 (σ x) X0
             grind)
          | exact superpose b0e232 b0e4945
          | (have j0 := b0e4945 X0
             grind)
          | exact resolve b0e4945 b0e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e232 b0e4945
        have b0e4966 : ∀ X0 : G, (σ x) = (M.op (σ x) y) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e4956 X0
             have i₂ := b0e664 (σ x)
             grind)
          | exact superpose b0e664 b0e4956
          | (have j0 := b0e4956 X0
             grind)
          | exact resolve b0e4956 b0e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4956
        have b0e4970 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b0e4966 X0
             grind)
          | (have r₁ := b0e4966 X0
             have r₂ := b0e1883
             grind)
          | exact resolve b0e4966 b0e1883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4966
        have b0e6085 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e2904 x
             have i₂ := b0e3982 x
             grind)
          | exact superpose b0e3982 b0e2904
          | (have j0 := b0e2904 x
             grind)
          | exact resolve b0e2904 b0e3982
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e2904 b0e3982
        have b0e6090 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b0e6085
        have b0e6120 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e6090
             have i₂ := b0e4970 (σ x)
             grind)
          | exact superpose b0e4970 b0e6090
          | exact resolve b0e6090 b0e4970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e4970 b0e6090
        have b0e6157 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b0e6120
             have i₂ := b0e664 (σ x)
             grind)
          | exact superpose b0e664 b0e6120
          | exact resolve b0e6120 b0e664
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e664 b0e6120
        have b0e6189 : False := by grind
        exact b0e6189
      · have b1e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X3) := by
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
        have b1e21 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e14 X0 y
             have i₂ := b1e18
             grind)
          | exact superpose b1e18 b1e14
          | (have j0 := b1e14 X0 y
             grind)
          | (have r₁ := b1e14 X0 y
             have r₂ := b1e18
             grind)
          | exact resolve b1e14 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e21 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21
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
        have b1e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b1e39 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e11 X0 (σ y) X1 X2
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e11
          | exact resolve b1e11 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e45 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y X1) := by
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
        have b1e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
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
        have b1e47 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X0 X4 X1 (M.op x x)
             have i₂ := b1e11 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b1e11 b1e11
          | exact resolve b1e11 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X3) = (M.op X1 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e11 X1 X0 X2 X3
             have i₂ := b1e15 X4 X0
             grind)
          | exact superpose b1e15 b1e11
          | (have j1 := b1e15 X4 X0
             grind)
          | exact resolve b1e11 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
        have b1e67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X3 X0) := by
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
        have b1e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e15 (σ X0) (σ X1)
             grind)
          | exact superpose b1e15 b1e16
          | (have j1 := b1e15 X0 (σ X1)
             grind)
          | exact resolve b1e16 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e65 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e76 : ∀ X0 X1 X4 : G, (M.op X1 (σ y)) = (M.op X1 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
          intro X0 X1 X4
          first
          | (have i₁ := b1e64 X0 X1 x x X4
             have i₂ := b1e39 X1 x x
             grind)
          | exact superpose b1e39 b1e64
          | (have j0 := b1e64 X0 X1 x x X4
             grind)
          | exact resolve b1e64 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e91 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b1e45 x X2
             have i₂ := b1e45 x X0
             grind)
          | (have i₁ := b1e45 X0 x
             have i₂ := b1e45 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e45 b1e45
          | exact resolve b1e45 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e122 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e18
             have i₂ := b1e91 y X0
             grind)
          | (have i₁ := b1e18
             have i₂ := b1e91 X0 y
             grind)
          | exact superpose b1e91 b1e18
          | exact resolve b1e18 b1e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e139 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b1e162 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e39 (σ y) (σ y) x
             have i₂ := b1e19
             grind)
          | exact superpose b1e19 b1e39
          | exact resolve b1e39 b1e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e417 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e46 X0 X1 y
             have i₂ := b1e122 y
             grind)
          | exact superpose b1e122 b1e46
          | exact resolve b1e46 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e122
        have b1e526 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e417 X0 (σ y)
             have i₂ := b1e162 (σ y)
             grind)
          | exact superpose b1e162 b1e417
          | exact resolve b1e417 b1e162
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e162
        have b1e547 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 y) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e11 X0 x X2 X3
             have i₂ := b1e417 X0 x
             grind)
          | exact superpose b1e417 b1e11
          | exact resolve b1e11 b1e417
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e842 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X2 X1) = (M.op X2 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e25 X0 X1
             have i₂ := b1e74 X1 (τ X0) X2
             grind)
          | exact superpose b1e74 b1e25
          | (have j1 := b1e74 X1 X1 X2
             grind)
          | exact resolve b1e25 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e854 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e74 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e855 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (k X2 X1) = (M.op X2 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e842 X0 X1 X2
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e842
          | (have j0 := b1e842 X0 X1 X2
             grind)
          | exact resolve b1e842 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e842
        have b1e885 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e17
             have i₂ := b1e526 (σ x)
             grind)
          | exact superpose b1e526 b1e17
          | exact resolve b1e17 b1e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1727 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 X1 X0
             have i₂ := b1e76 X0 X0 X2
             grind)
          | (have i₁ := b1e15 X0 (σ y)
             have i₂ := b1e76 X0 (σ y) x
             grind)
          | exact superpose b1e76 b1e15
          | (have j0 := b1e15 X1 X0
             have j1 := b1e76 X0 X1 X1
             grind)
          | exact resolve b1e15 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e1797 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 y) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1727 X0 X2 X1
             have i₂ := b1e526 X0
             grind)
          | exact superpose b1e526 b1e1727
          | (have j0 := b1e1727 X0 X2 X2
             grind)
          | exact resolve b1e1727 b1e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1727
        have b1e2090 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op X1 X0) ∨ (k X3 X1) = (M.op X3 X1) ∨ (k X4 X0) = (M.op X4 X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e67 X1 X0 X2 X3
             have i₂ := b1e15 X4 X0
             grind)
          | exact superpose b1e15 b1e67
          | (have j0 := b1e67 X1 X1 X2 X3
             have j1 := b1e15 X3 X1
             grind)
          | exact resolve b1e67 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e2412 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
          intro X0
          first
          | (have i₁ := b1e139 X0 y
             have i₂ := b1e24 (σ X0)
             grind)
          | exact superpose b1e24 b1e139
          | exact resolve b1e139 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e2420 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2412 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2412
          | exact resolve b1e2412 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2412
        have b1e2595 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e139 X0 (τ y)
             have i₂ := b1e2420 (σ X0)
             grind)
          | exact superpose b1e2420 b1e139
          | exact resolve b1e139 b1e2420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2420
        have b1e2598 : ∀ X0 : G, (k X0 (τ (τ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2595 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2595
          | exact resolve b1e2595 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2595
        have b1e2684 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e72 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e2759 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (τ y)))) := by
          intro X0
          first
          | (have i₁ := b1e139 X0 (τ (τ y))
             have i₂ := b1e2598 (σ X0)
             grind)
          | exact superpose b1e2598 b1e139
          | exact resolve b1e139 b1e2598
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2598
        have b1e2762 : ∀ X0 : G, (k X0 (τ (τ (τ y)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e2759 X0
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e2759
          | exact resolve b1e2759 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2759
        have b1e3445 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X0 X2) X3) ∨ (M.op (M.op X0 X2) X3) = (k (M.op (M.op X0 X2) X3) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e854 (M.op (M.op X0 X2) X3) X4
             have i₂ := b1e47 X0 X2 X3 X4 X1
             grind)
          | exact superpose b1e47 b1e854
          | (have j0 := b1e854 (M.op (M.op X0 X2) X3) X4
             grind)
          | exact resolve b1e854 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e3471 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 X2) X3) = (k (M.op (M.op X0 X2) X3) X4) := by
          intro X0 X2 X3 X4
          first
          | (have j0 := b1e3445 X0 x X2 X3 X4
             grind)
          | (have r₁ := b1e3445 X0 x X2 X3 X4
             have r₂ := b1e11 X0 x X2 X3
             grind)
          | exact resolve b1e3445 b1e11
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3445
        have b1e3488 : ∀ X0 X4 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) X4) := by
          intro X0 X4
          first
          | (have i₁ := b1e3471 X0 x x X4
             have i₂ := b1e39 X0 x x
             grind)
          | exact superpose b1e39 b1e3471
          | exact resolve b1e3471 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3471
        have b1e3501 : ∀ X0 X4 : G, (M.op X0 y) = (k (M.op X0 y) X4) := by
          intro X0 X4
          first
          | (have i₁ := b1e3488 X0 X4
             have i₂ := b1e526 X0
             grind)
          | exact superpose b1e526 b1e3488
          | exact resolve b1e3488 b1e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3488
        have b1e3559 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e26 X1 X0
             have i₂ := b1e855 X2 (τ X1) X0
             grind)
          | exact superpose b1e855 b1e26
          | (have j1 := b1e855 X2 (τ X1) X2
             grind)
          | exact resolve b1e26 b1e855
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e855
        have b1e3574 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e3559 X0 X1 X2
             have i₂ := b1e13 X1
             grind)
          | exact superpose b1e13 b1e3559
          | (have j0 := b1e3559 X0 X1 X2
             grind)
          | exact resolve b1e3559 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3559
        have b1e5345 : (σ (τ (τ (τ y)))) ≠ (σ (τ (τ (τ y)))) ∨ (σ (τ (τ (τ y)))) = (M.op (σ (τ (τ (τ y)))) (σ (τ (τ (τ y))))) := by
          first
          | (have i₁ := b1e2684 (τ (τ (τ y)))
             have i₂ := b1e2762 (τ (τ (τ y)))
             grind)
          | exact superpose b1e2762 b1e2684
          | (have j0 := b1e2684 (τ (τ (τ y)))
             grind)
          | exact resolve b1e2684 b1e2762
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2762
        have b1e5359 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e2684 (τ X0)
             have i₂ := b1e26 X0 (τ X0)
             grind)
          | exact superpose b1e26 b1e2684
          | (have j0 := b1e2684 (τ X0)
             grind)
          | exact resolve b1e2684 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2684
        have b1e5370 : (σ (τ (τ (τ y)))) = (M.op (σ (τ (τ (τ y)))) (σ (τ (τ (τ y))))) := by grind
        clear b1e5345
        have b1e5385 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e5359 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e5359
          | (have j0 := b1e5359 X0
             grind)
          | exact resolve b1e5359 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5359
        have b1e5393 : (τ (τ y)) = (M.op (τ (τ y)) (τ (τ y))) := by
          first
          | (have i₁ := b1e5370
             have i₂ := b1e13 (τ (τ y))
             grind)
          | exact superpose b1e13 b1e5370
          | exact resolve b1e5370 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5370
        have b1e5402 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e5385 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e5385
          | (have j0 := b1e5385 X0
             grind)
          | exact resolve b1e5385 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5385
        have b1e9260 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e1797 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1797
        have b1e9261 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 y) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e9260 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9260
        have b1e10312 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (τ y))) := by
          intro X0
          first
          | (have i₁ := b1e417 X0 (τ (τ y))
             have i₂ := b1e5393
             grind)
          | exact superpose b1e5393 b1e417
          | exact resolve b1e417 b1e5393
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e417 b1e5393
        have b1e13328 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e2090 X2 X1 X1 X0 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2090
        have b1e13329 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e13328 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13328
        have b1e33517 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (k X1 x) = (M.op X1 x) := by
          intro X0 X1
          first
          | (have i₁ := b1e20
             have i₂ := b1e13329 X1 x X0
             grind)
          | (have i₁ := b1e20
             have i₂ := b1e13329 X0 x x
             grind)
          | exact superpose b1e13329 b1e20
          | (have j1 := b1e13329 X1 x x
             grind)
          | exact resolve b1e20 b1e13329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33538 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e854 X0 X1
             have i₂ := b1e13329 X2 X0 X1
             grind)
          | (have i₁ := b1e854 X1 X1
             have i₂ := b1e13329 X0 X1 X2
             grind)
          | exact superpose b1e13329 b1e854
          | (have j0 := b1e854 X0 X0
             have j1 := b1e13329 X2 X0 X2
             grind)
          | exact resolve b1e854 b1e13329
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e854 b1e13329
        have b1e33819 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e33538 X0 X1 X2
             have j1 := b1e15 X2 X0
             grind)
          | (have r₁ := b1e33538 X1 X1 X2
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e33538 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33538
        have b1e33948 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e33517 (τ (τ y)) X0
             have i₂ := b1e10312 x
             grind)
          | exact superpose b1e10312 b1e33517
          | (have j0 := b1e33517 y X0
             grind)
          | exact resolve b1e33517 b1e10312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10312 b1e33517
        have b1e33950 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b1e33948 X0
             have j1 := b1e9261 X0 x
             grind)
          | (have r₁ := b1e33948 X0
             have r₂ := b1e9261 X0 x
             grind)
          | exact resolve b1e33948 b1e9261
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9261 b1e33948
        have b1e34914 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e139 X0 x
             have i₂ := b1e33950 (σ X0)
             grind)
          | exact superpose b1e33950 b1e139
          | exact resolve b1e139 b1e33950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34923 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) := by
          intro X0
          first
          | (have i₁ := b1e25 X0 x
             have i₂ := b1e33950 (τ X0)
             grind)
          | exact superpose b1e33950 b1e25
          | exact resolve b1e25 b1e33950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e35195 : ∀ X0 X1 : G, (k (k X0 (τ X1)) (τ x)) = (τ (M.op (k (σ X0) X1) x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e34914 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e34914
          | exact resolve b1e34914 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e34914
        have b1e38302 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e34 X0 X1
             have i₂ := b1e33819 X0 (σ X1) X2
             grind)
          | exact superpose b1e33819 b1e34
          | (have j1 := b1e33819 (τ X0) X1 X2
             grind)
          | exact resolve b1e34 b1e33819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e33819
        have b1e38590 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 y)) = (k (σ (M.op X0 X1)) X2) ∨ (k X3 X2) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e3574 (M.op X0 X1) X2 X3
             have i₂ := b1e547 X0 X1 (τ X2)
             grind)
          | exact superpose b1e547 b1e3574
          | (have j0 := b1e3574 X0 X2 X3
             grind)
          | exact resolve b1e3574 b1e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e547 b1e3574
        have b1e147789 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) x) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e33950 (τ X0)
             have i₂ := b1e38302 X0 x X1
             grind)
          | exact superpose b1e38302 b1e33950
          | (have j1 := b1e38302 X0 X1 X1
             grind)
          | exact resolve b1e33950 b1e38302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38302
        have b1e169857 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 x) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e147789 (σ X0) X1
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e147789
          | (have j0 := b1e147789 (σ X0) X1
             grind)
          | exact resolve b1e147789 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147789
        have b1e236789 : ∀ X0 : G, (τ (M.op (M.op (σ X0) x) x)) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e35195 X0 x
             have i₂ := b1e33950 (σ X0)
             grind)
          | exact superpose b1e33950 b1e35195
          | exact resolve b1e35195 b1e33950
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33950 b1e35195
        have b1e236811 : ∀ X0 : G, (τ (M.op (σ X0) (σ y))) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e236789 X0
             have i₂ := b1e39 (σ X0) x x
             grind)
          | exact superpose b1e39 b1e236789
          | exact resolve b1e236789 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e236789
        have b1e236890 : ∀ X0 : G, (τ (M.op (σ X0) y)) = (k (k X0 (τ x)) (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e236811 X0
             have i₂ := b1e526 (σ X0)
             grind)
          | exact superpose b1e526 b1e236811
          | exact resolve b1e236811 b1e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e236811
        have b1e286418 : ∀ X0 X1 X2 X3 : G, (τ (σ (M.op X0 y))) = (k (M.op X0 X1) (τ X2)) ∨ (k X3 X2) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e139 (M.op X0 X1) X2
             have i₂ := b1e38590 X0 X1 X2 X3
             grind)
          | exact superpose b1e38590 b1e139
          | (have j1 := b1e38590 X0 X1 X2 X3
             grind)
          | exact resolve b1e139 b1e38590
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139 b1e38590
        have b1e286464 : ∀ X0 X1 X2 X3 : G, (M.op X0 y) = (k (M.op X0 X1) (τ X2)) ∨ (k X3 X2) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e286418 X0 X1 X2 X3
             have i₂ := b1e12 (M.op X0 y)
             grind)
          | exact superpose b1e12 b1e286418
          | (have j0 := b1e286418 X0 X1 X2 X3
             grind)
          | exact resolve b1e286418 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e286418
        have b1e286664 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 y) = (k (M.op X1 X2) (τ X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5402 X0
             have i₂ := b1e286464 X1 X2 X0 X0
             grind)
          | exact superpose b1e286464 b1e5402
          | (have j0 := b1e5402 X0
             have j1 := b1e286464 X1 X2 X0 x
             grind)
          | (have r₁ := b1e5402 X2
             have r₂ := b1e286464 X0 X1 X2 X2
             grind)
          | exact resolve b1e5402 b1e286464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5402 b1e286464
        have b1e286673 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X1 y) = (k (M.op X1 X2) (τ X0)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e286664 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e286664
        have b1e287707 : ∀ X0 X1 : G, (k (M.op X0 y) (τ x)) = (τ (M.op (σ (M.op X0 X1)) y)) ∨ x = (M.op x x) := by
          intro X0 X1
          first
          | (have i₁ := b1e236890 (M.op X0 X1)
             have i₂ := b1e286673 x X0 X1
             grind)
          | exact superpose b1e286673 b1e236890
          | (have j1 := b1e286673 x X1 x
             grind)
          | exact resolve b1e236890 b1e286673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e236890 b1e286673
        have b1e287711 : ∀ X0 X1 : G, (k (M.op X0 y) (τ x)) = (τ (M.op (σ (M.op X0 X1)) y)) := by
          intro X0 X1
          first
          | (have j0 := b1e287707 X0 X1
             grind)
          | (have r₁ := b1e287707 X0 X1
             have r₂ := b1e20
             grind)
          | exact resolve b1e287707 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e287707
        have b1e287752 : ∀ X0 X1 : G, (M.op X0 y) = (τ (M.op (σ (M.op X0 X1)) y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e287711 X0 X1
             have i₂ := b1e3501 X0 (τ x)
             grind)
          | exact superpose b1e3501 b1e287711
          | exact resolve b1e287711 b1e3501
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3501 b1e287711
        have b1e288087 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (k X0 (σ x)) y)) := by
          intro X0
          first
          | (have i₁ := b1e287752 (τ X0) x
             have i₂ := b1e34923 X0
             grind)
          | exact superpose b1e34923 b1e287752
          | exact resolve b1e287752 b1e34923
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34923 b1e287752
        have b1e289407 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (M.op X0 (σ x)) y)) ∨ x = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b1e288087 X0
             have i₂ := b1e169857 x X0
             grind)
          | exact superpose b1e169857 b1e288087
          | (have j1 := b1e169857 x x
             grind)
          | exact resolve b1e288087 b1e169857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e169857 b1e288087
        have b1e289608 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (M.op X0 (σ x)) y)) := by
          intro X0
          first
          | (have j0 := b1e289407 X0
             grind)
          | (have r₁ := b1e289407 X0
             have r₂ := b1e20
             grind)
          | exact resolve b1e289407 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e289407
        have b1e289674 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e289608 X0
             have i₂ := b1e39 X0 (σ x) y
             grind)
          | exact superpose b1e39 b1e289608
          | exact resolve b1e289608 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e289608
        have b1e289693 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e289674 X0
             have i₂ := b1e526 X0
             grind)
          | exact superpose b1e526 b1e289674
          | exact resolve b1e289674 b1e526
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e526 b1e289674
        have b1e289948 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
          intro X0
          first
          | (have i₁ := b1e13 (M.op X0 y)
             have i₂ := b1e289693 X0
             grind)
          | exact superpose b1e289693 b1e13
          | exact resolve b1e13 b1e289693
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e289693
        have b1e290181 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
          intro X0
          first
          | (have i₁ := b1e289948 (σ X0)
             have i₂ := b1e12 X0
             grind)
          | exact superpose b1e12 b1e289948
          | exact resolve b1e289948 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e289948
        have b1e290984 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e885
             have i₂ := b1e290181 x
             grind)
          | exact superpose b1e290181 b1e885
          | (have r₁ := b1e885
             have r₂ := b1e290181 x
             grind)
          | exact resolve b1e885 b1e290181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e885 b1e290181
        have b1e291123 : False := by grind
        exact b1e291123
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
        have b2e63 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
        have b2e70 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e63 X0
             grind)
          | (have r₁ := b2e63 (σ y)
             have r₂ := b2e19
             grind)
          | (have r₁ := b2e63 X0
             have r₂ := b2e19
             grind)
          | exact resolve b2e63 b2e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e100 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e70 (σ y)
             grind)
          | exact superpose b2e70 b2e19
          | (have r₁ := b2e19
             have r₂ := b2e70 (σ y)
             grind)
          | exact resolve b2e19 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e102 : False := by grind
        exact b2e102
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
        have b3e59 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
        have b3e62 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e59 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
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
          | (have i₁ := b3e62 X0
             have i₂ := b3e117 X0
             grind)
          | exact superpose b3e117 b3e62
          | exact resolve b3e62 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62 b3e117
        have b3e143 : (σ y) ≠ (σ y) := by
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
        have b3e147 : False := by grind
        exact b3e147
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
        have b4e65 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
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
        have b4e70 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b4e65 X0
             grind)
          | (have r₁ := b4e65 y
             have r₂ := b4e18
             grind)
          | (have r₁ := b4e65 X0
             have r₂ := b4e18
             grind)
          | exact resolve b4e65 b4e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e65
        have b4e81 : y ≠ y := by
          first
          | (have i₁ := b4e18
             have i₂ := b4e70 y
             grind)
          | exact superpose b4e70 b4e18
          | (have r₁ := b4e18
             have r₂ := b4e70 y
             grind)
          | exact resolve b4e18 b4e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b4e70
        have b4e82 : False := by grind
        exact b4e82
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
        have b5e69 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
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
        have b5e74 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b5e69 X0
             grind)
          | (have r₁ := b5e69 y
             have r₂ := b5e18
             grind)
          | (have r₁ := b5e69 X0
             have r₂ := b5e18
             grind)
          | exact resolve b5e69 b5e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e69
        have b5e85 : y ≠ y := by
          first
          | (have i₁ := b5e18
             have i₂ := b5e74 y
             grind)
          | exact superpose b5e74 b5e18
          | (have r₁ := b5e18
             have r₂ := b5e74 y
             grind)
          | exact resolve b5e18 b5e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b5e74
        have b5e86 : False := by grind
        exact b5e86
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b6e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e19 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht he hd nh hM hi1 hi2 h0a h1a h2a
        have b6e55 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e14 X1 X0
             have i₂ := b6e15 X2 X0
             grind)
          | exact superpose b6e15 b6e14
          | (have j0 := b6e14 X1 X0
             have j1 := b6e15 X2 X0
             grind)
          | (have r₁ := b6e14 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e14 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
        have b6e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e15 (σ X0) (σ X1)
             grind)
          | exact superpose b6e15 b6e16
          | (have j1 := b6e15 X0 (σ X1)
             grind)
          | exact resolve b6e16 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e59 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e63 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e55 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e91 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e16 X0 y
             have i₂ := b6e62 (σ X0)
             grind)
          | exact superpose b6e62 b6e16
          | exact resolve b6e16 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e2406 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e91 y
             grind)
          | exact superpose b6e91 b6e19
          | exact resolve b6e19 b6e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91
        have b6e2572 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e2406
             have i₂ := b6e63 y y X0
             grind)
          | exact superpose b6e63 b6e2406
          | (have j1 := b6e63 y x X0
             grind)
          | exact resolve b6e2406 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e2406
        have b6e2574 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b6e2572 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2572
        have b6e2593 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e17
             have i₂ := b6e61 x y
             grind)
          | exact superpose b6e61 b6e17
          | (have j1 := b6e61 x y
             grind)
          | exact resolve b6e17 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e2680 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b6e2593
             have r₂ := b6e19
             grind)
          | exact resolve b6e2593 b6e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2593
        have b6e2695 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e2680
             have i₂ := b6e2574 x
             grind)
          | exact superpose b6e2574 b6e2680
          | exact resolve b6e2680 b6e2574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2574 b6e2680
        have b6e2696 : False := by grind
        exact b6e2696
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
        have b7e49 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
        have b7e53 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
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
        have b7e57 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b7e53 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e53
        have b7e58 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b7e49 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e49
        have b7e60 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b7e16 X0 y
             have i₂ := b7e57 (σ X0)
             grind)
          | exact superpose b7e57 b7e16
          | exact resolve b7e16 b7e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e57
        have b7e193 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have i₁ := b7e19
             have i₂ := b7e60 y
             grind)
          | exact superpose b7e60 b7e19
          | exact resolve b7e19 b7e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b7e194 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b7e17
             have i₂ := b7e60 x
             grind)
          | exact superpose b7e60 b7e17
          | exact resolve b7e17 b7e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e60
        have b7e282 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b7e193
             have i₂ := b7e58 y y X0
             grind)
          | exact superpose b7e58 b7e193
          | (have j1 := b7e58 y x X0
             grind)
          | exact resolve b7e193 b7e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e58 b7e193
        have b7e284 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b7e282 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e282
        have b7e966 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b7e194
             have i₂ := b7e284 x
             grind)
          | exact superpose b7e284 b7e194
          | exact resolve b7e194 b7e284
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b7e194 b7e284
        have b7e972 : False := by grind
        exact b7e972

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4485 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4485 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
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
      have b0e33 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (σ x) X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 x X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X0 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | (have i₁ := b0e10 (M.op X1 X2) X1 X2
           have i₂ := b0e10 (M.op X1 X1) X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 X2 (M.op X0 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | (have i₁ := b0e10 X0 (M.op X1 X2) X0
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X0 X0) X2 X3
           have i₂ := b0e10 (M.op X2 X3) X0 X1
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X0))) := by
        intro X0 X1
        grind
      have b0e45 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 X0 y
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e10 X0 y X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e10
        | exact resolve b0e10 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X1)) = X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op X1 X1) X1 X2
           have i₂ := b0e14 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 (M.op X1 X1))
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 (M.op X1 X1) X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X1)) = X0 ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op X1 X2) X1 X2
           have i₂ := b0e14 (M.op X1 X2) X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op (M.op X1 X2) X0)
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 (M.op X1 X2) X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b0e125 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e33 X0 y
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e33
        | exact resolve b0e33 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e148 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e125 X0
           have i₂ := b0e10 X0 y (σ x)
           grind)
        | exact superpose b0e10 b0e125
        | exact resolve b0e125 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125
      have b0e200 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ y) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 X0 X1 X2 (σ y)
           have i₂ := b0e39 X0
           grind)
        | (have i₁ := b0e35 (σ y) X1 X2 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e35
        | exact resolve b0e35 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e201 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 X0 X1 X2 y
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e35 y X1 X2 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e35
        | exact resolve b0e35 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e209 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 x X0 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e35
        | exact resolve b0e35 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e252 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e200 X0 X1 X2
           have i₂ := b0e201 (σ y) X0 X2
           grind)
        | exact superpose b0e201 b0e200
        | exact resolve b0e200 b0e201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e200
      have b0e265 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op y y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e252 X0 X1 X2
           have i₂ := b0e10 X2 y (σ y)
           grind)
        | exact superpose b0e10 b0e252
        | exact resolve b0e252 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252
      have b0e274 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e265 X0 X1 X2
           have i₂ := b0e148 X2
           grind)
        | exact superpose b0e148 b0e265
        | exact resolve b0e265 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e265
      have b0e281 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e209 (M.op X0 X0) X2
           have i₂ := b0e10 x X0 X1
           grind)
        | exact superpose b0e10 b0e209
        | exact resolve b0e209 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e209
      have b0e312 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e281 X0 X1 X2
           have i₂ := b0e201 (M.op X0 X1) x X2
           grind)
        | exact superpose b0e201 b0e281
        | exact resolve b0e281 b0e201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e281
      have b0e316 : ∀ X2 : G, (M.op X2 (M.op y y)) = (M.op y X2) := by
        intro X2
        first
        | (have i₁ := b0e312 x x X2
           have i₂ := b0e10 X2 y (M.op x x)
           grind)
        | exact superpose b0e10 b0e312
        | exact resolve b0e312 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e312
      have b0e325 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e55 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e353 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b0e34 X0 (M.op y y)
           have i₂ := b0e316 x
           grind)
        | exact superpose b0e316 b0e34
        | exact resolve b0e34 b0e316
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e354 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e353 X0
           have i₂ := b0e274 y x X0
           grind)
        | exact superpose b0e274 b0e353
        | exact resolve b0e353 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e353
      have b0e496 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X2 X3) (M.op X2 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X0 (M.op X2 X3) X1
           have i₂ := b0e37 X2 X3 X1 X0
           grind)
        | (have i₁ := b0e10 (M.op X2 X2) X1 X2
           have i₂ := b0e37 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e517 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y (M.op X2 X3)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e496 X0 X1 X2 X3
           have i₂ := b0e45 (M.op X2 X3) X0
           grind)
        | exact superpose b0e45 b0e496
        | exact resolve b0e496 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e496
      have b0e576 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e517 X0 X1 x x
           have i₂ := b0e10 X0 y (M.op x x)
           grind)
        | exact superpose b0e10 b0e517
        | exact resolve b0e517 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e517
      have b0e629 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e576 X0 X1
           have i₂ := b0e148 X0
           grind)
        | exact superpose b0e148 b0e576
        | exact resolve b0e576 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e576
      have b0e674 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e629 X0 X1
           have i₂ := b0e354 X0
           grind)
        | exact superpose b0e354 b0e629
        | exact resolve b0e629 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e629
      have b0e799 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e39 X0
           have i₂ := b0e354 X0
           grind)
        | exact superpose b0e354 b0e39
        | exact resolve b0e39 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e815 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e354 (σ x)
           grind)
        | exact superpose b0e354 b0e16
        | exact resolve b0e16 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e820 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e815
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e815
        | exact resolve b0e815 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e815
      have b0e3014 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e674 X0 X1
           grind)
        | exact superpose b0e674 b0e10
        | exact resolve b0e10 b0e674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8770 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e60 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e9236 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e43 X1 X2
           have i₂ := b0e57 X0 X1 X2
           grind)
        | (have i₁ := b0e43 X0 X1
           have i₂ := b0e57 (M.op (M.op X0 X1) (M.op X0 X0)) X1 X2
           grind)
        | exact superpose b0e57 b0e43
        | (have j1 := b0e57 X0 X1 X2
           grind)
        | exact resolve b0e43 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e57
      have b0e9347 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (k (M.op X1 X1) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e9236 X0 X1 X2
           have i₂ := b0e274 X1 X1 X0
           grind)
        | exact superpose b0e274 b0e9236
        | (have j0 := b0e9236 X0 X1 X2
           grind)
        | exact resolve b0e9236 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9236
      have b0e9491 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e9347 X0 X1 X2
           have i₂ := b0e354 X0
           grind)
        | exact superpose b0e354 b0e9347
        | (have j0 := b0e9347 X0 X1 X2
           grind)
        | exact resolve b0e9347 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9347
      have b0e11166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X3 X3)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e41 (M.op X1 X2) (M.op X1 X1) X3 X4
           have i₂ := b0e58 X0 X1 X2
           grind)
        | (have i₁ := b0e41 X0 X1 X2 X3
           have i₂ := b0e58 (M.op X0 X1) X1 X2
           grind)
        | exact superpose b0e58 b0e41
        | (have j1 := b0e58 X0 X1 X2
           grind)
        | exact resolve b0e41 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e58
      have b0e11190 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y (M.op X1 X2)) (M.op X3 X3)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11166 X0 X1 X2 X3 X4
           have i₂ := b0e201 (M.op X1 X2) (M.op X1 X2) (M.op X3 X3)
           grind)
        | exact superpose b0e201 b0e11166
        | (have j0 := b0e11166 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11166 b0e201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e201 b0e11166
      have b0e11365 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11190 X0 X1 X2 X3 X4
           have i₂ := b0e10 (M.op X3 X3) y (M.op X1 X2)
           grind)
        | exact superpose b0e10 b0e11190
        | (have j0 := b0e11190 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11190 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11190
      have b0e11540 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y y) (σ y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11365 X0 X1 X2 X3 X4
           have i₂ := b0e274 X3 X3 (M.op y y)
           grind)
        | exact superpose b0e274 b0e11365
        | (have j0 := b0e11365 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11365 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11365
      have b0e11709 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ y) (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11540 X0 X1 X2 X3 X4
           have i₂ := b0e10 (σ y) y y
           grind)
        | exact superpose b0e10 b0e11540
        | (have j0 := b0e11540 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11540 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11540
      have b0e11857 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y y) y) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11709 X0 X1 X2 X3 X4
           have i₂ := b0e799 (M.op y y)
           grind)
        | exact superpose b0e799 b0e11709
        | (have j0 := b0e11709 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11709 b0e799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e799 b0e11709
      have b0e11994 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11857 X0 X1 X2 X3 X4
           have i₂ := b0e10 y y y
           grind)
        | exact superpose b0e10 b0e11857
        | (have j0 := b0e11857 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11857 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11857
      have b0e12129 : ∀ X0 X1 X2 X3 X4 : G, (M.op y y) = (M.op X0 (M.op X3 X4)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11994 X0 X1 X2 X3 X4
           have i₂ := b0e674 y y
           grind)
        | exact superpose b0e674 b0e11994
        | (have j0 := b0e11994 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e11994 b0e674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11994
      have b0e12259 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (σ y)) = (k (M.op X1 X2) X0) ∨ (M.op y y) = (M.op X0 (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e12129 X0 X1 X2 X3 X4
           have i₂ := b0e274 X1 X2 X0
           grind)
        | exact superpose b0e274 b0e12129
        | (have j0 := b0e12129 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e12129 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e274 b0e12129
      have b0e12361 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 y) = (k (M.op X1 X2) X0) ∨ (M.op y y) = (M.op X0 (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e12259 X0 X1 X2 X3 X4
           have i₂ := b0e354 X0
           grind)
        | exact superpose b0e354 b0e12259
        | (have j0 := b0e12259 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e12259 b0e354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e354 b0e12259
      have b0e13286 : ∀ X0 X1 : G, (M.op X0 y) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e325 X0 (M.op X1 X1)
           have i₂ := b0e674 X0 X1
           grind)
        | exact superpose b0e674 b0e325
        | (have j0 := b0e325 X0 y
           grind)
        | exact resolve b0e325 b0e674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325
      have b0e28591 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e13286 X0 X1
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e13286 y X1
           have i₂ := b0e40 y
           grind)
        | exact superpose b0e40 b0e13286
        | (have j0 := b0e13286 X0 X1
           grind)
        | exact resolve b0e13286 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13286
      have b0e31179 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op y y) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e28591 (M.op y y) X0
           have i₂ := b0e316 y
           grind)
        | exact superpose b0e316 b0e28591
        | (have j0 := b0e28591 (M.op y y) X0
           grind)
        | (have r₁ := b0e28591 (M.op y y) x
           have r₂ := b0e316 y
           grind)
        | exact resolve b0e28591 b0e316
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e316 b0e28591
      have b0e31185 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e31179 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31179
      have b0e47860 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e8770 (M.op y y)
           have i₂ := b0e31185 y
           grind)
        | exact superpose b0e31185 b0e8770
        | (have j0 := b0e8770 (M.op y y)
           grind)
        | exact resolve b0e8770 b0e31185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8770 b0e31185
      have b0e47873 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b0e47860
      have b0e78158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 y) ∨ (M.op X1 y) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e9491 X1 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9491
      have b0e83758 : ∀ X0 X2 X3 : G, (M.op X0 y) = (M.op y y) ∨ (M.op X0 y) = (k (M.op X2 X3) X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e674 X0 x
           have i₂ := b0e12361 X0 X2 X3 x x
           grind)
        | exact superpose b0e12361 b0e674
        | (have j1 := b0e12361 X0 X2 X3 X3 x
           grind)
        | exact resolve b0e674 b0e12361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12361
      have b0e170865 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e674 X0 (σ (M.op y y))
           have i₂ := b0e47873
           grind)
        | exact superpose b0e47873 b0e674
        | exact resolve b0e674 b0e47873
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e674
      have b0e170927 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e3014 X0 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b0e47873
           grind)
        | exact superpose b0e47873 b0e3014
        | exact resolve b0e3014 b0e47873
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3014
      have b0e171447 : (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
        first
        | (have i₁ := b0e47873
           have i₂ := b0e170865 (σ (M.op y y))
           grind)
        | exact superpose b0e170865 b0e47873
        | exact resolve b0e47873 b0e170865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47873 b0e170865
      have b0e171521 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e171447
           have i₂ := b0e170927 y
           grind)
        | exact superpose b0e170927 b0e171447
        | exact resolve b0e171447 b0e170927
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171447
      have b0e172091 : ∀ X0 : G, (k (M.op y y) (σ X0)) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 (M.op y y) X0
           have i₂ := b0e171521
           grind)
        | exact superpose b0e171521 b0e15
        | exact resolve b0e15 b0e171521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171521
      have b0e187416 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (σ (M.op y y)) y) ∨ (M.op X0 y) = (k (M.op (σ (M.op y y)) y) X0) := by
        intro X0
        first
        | (have i₁ := b0e78158 (σ (M.op y y)) x
           have i₂ := b0e170927 (σ (M.op y y))
           grind)
        | exact superpose b0e170927 b0e78158
        | (have r₁ := b0e78158 y (σ (M.op y y))
           have r₂ := b0e170927 y
           grind)
        | (have r₁ := b0e78158 (σ (M.op y y)) (σ (M.op y y))
           have r₂ := b0e170927 (σ (M.op y y))
           grind)
        | exact resolve b0e78158 b0e170927
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78158
      have b0e187473 : ∀ X0 : G, (M.op X0 y) ≠ (M.op y y) ∨ (M.op X0 y) = (k (M.op (σ (M.op y y)) y) X0) := by
        intro X0
        first
        | (have i₁ := b0e187416 X0
           have i₂ := b0e170927 y
           grind)
        | exact superpose b0e170927 b0e187416
        | (have j0 := b0e187416 X0
           grind)
        | (have r₁ := b0e187416 y
           have r₂ := b0e170927 y
           grind)
        | exact resolve b0e187416 b0e170927
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187416
      have b0e187509 : ∀ X0 : G, (M.op X0 y) = (k (M.op (σ (M.op y y)) y) X0) := by
        intro X0
        first
        | (have j0 := b0e187473 X0
           have j1 := b0e83758 X0 (σ (M.op y y)) y
           grind)
        | (have r₁ := b0e187473 X0
           have r₂ := b0e83758 X0 x x
           grind)
        | (have r₁ := b0e187473 y
           have r₂ := b0e83758 y x x
           grind)
        | exact resolve b0e187473 b0e83758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83758 b0e187473
      have b0e187538 : ∀ X0 : G, (M.op X0 y) = (k (M.op y y) X0) := by
        intro X0
        first
        | (have i₁ := b0e187509 X0
           have i₂ := b0e170927 y
           grind)
        | exact superpose b0e170927 b0e187509
        | exact resolve b0e187509 b0e170927
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170927 b0e187509
      have b0e187667 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e172091 X0
           have i₂ := b0e187538 (σ X0)
           grind)
        | exact superpose b0e187538 b0e172091
        | exact resolve b0e172091 b0e187538
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172091
      have b0e187779 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e187667 X0
           have i₂ := b0e187538 X0
           grind)
        | exact superpose b0e187538 b0e187667
        | exact resolve b0e187667 b0e187538
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e187538 b0e187667
      have b0e187816 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e187779 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e187779
        | exact resolve b0e187779 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e187779
      have b0e189341 : (M.op y (σ x)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e820
           have i₂ := b0e187816 x
           grind)
        | exact superpose b0e187816 b0e820
        | (have r₁ := b0e820
           have r₂ := b0e187816 x
           grind)
        | exact resolve b0e820 b0e187816
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e820 b0e187816
      have b0e189383 : False := by grind
      exact b0e189383
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e10 (M.op X1 X2) X1 X2
           have i₂ := b1e10 (M.op X1 X1) X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
      have b1e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 X2 (M.op X0 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X2) X0
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X0 X0) X2 X3
           have i₂ := b1e10 (M.op X2 X3) X0 X1
           grind)
        | (have i₁ := b1e10 X0 X1 X2
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e41 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 X0 y
           have i₂ := b1e34 X0
           grind)
        | (have i₁ := b1e10 X0 y X0
           have i₂ := b1e34 X0
           grind)
        | exact superpose b1e34 b1e10
        | exact resolve b1e10 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b1e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b1e93 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e115 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e32 X2 X3 X4 (M.op X0 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e32 (M.op X1 X2) X1 X2 X0
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e32
        | exact resolve b1e32 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e116 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 X0 X1 X2 y
           have i₂ := b1e34 X0
           grind)
        | (have i₁ := b1e32 y X1 X2 X0
           have i₂ := b1e34 X0
           grind)
        | exact superpose b1e34 b1e32
        | exact resolve b1e32 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e122 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e32 x X0 X1 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e32
        | exact resolve b1e32 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e154 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (M.op y (M.op X0 X1)) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e115 X0 X1 X2 X3 X4
           have i₂ := b1e116 (M.op X0 X1) X2 X4
           grind)
        | exact superpose b1e116 b1e115
        | exact resolve b1e115 b1e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e115
      have b1e160 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op X4 (M.op y y)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e154 x x X2 X3 X4
           have i₂ := b1e10 X4 y (M.op x x)
           grind)
        | exact superpose b1e10 b1e154
        | exact resolve b1e154 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e154
      have b1e164 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e122 (M.op X0 X0) X2
           have i₂ := b1e10 x X0 X1
           grind)
        | exact superpose b1e10 b1e122
        | exact resolve b1e122 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e122
      have b1e193 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e164 X0 X1 X2
           have i₂ := b1e116 (M.op X0 X1) x X2
           grind)
        | exact superpose b1e116 b1e164
        | exact resolve b1e164 b1e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e164
      have b1e196 : ∀ X2 : G, (M.op y X2) = (M.op X2 (M.op y y)) := by
        intro X2
        first
        | (have i₁ := b1e193 x x X2
           have i₂ := b1e10 X2 y (M.op x x)
           grind)
        | exact superpose b1e10 b1e193
        | exact resolve b1e193 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e193
      have b1e203 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X2 X2) (M.op X3 X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 (M.op X2 X2) X3 X4
           have i₂ := b1e35 X0 X1 X2 (M.op X3 X4)
           grind)
        | (have i₁ := b1e10 X3 (M.op X0 X1) X2
           have i₂ := b1e35 X0 X1 X2 X3
           grind)
        | exact superpose b1e35 b1e10
        | exact resolve b1e10 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e316 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X2 X3) (M.op X2 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 (M.op X2 X3) X1
           have i₂ := b1e35 X2 X3 X1 X0
           grind)
        | (have i₁ := b1e10 (M.op X2 X2) X1 X2
           have i₂ := b1e35 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact superpose b1e35 b1e10
        | exact resolve b1e10 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35
      have b1e333 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y (M.op X2 X3)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e316 X0 X1 X2 X3
           have i₂ := b1e41 (M.op X2 X3) X0
           grind)
        | exact superpose b1e41 b1e316
        | exact resolve b1e316 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e316
      have b1e340 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op y (M.op X0 X1)) (M.op X3 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e308 X0 X1 X2 X3 X4
           have i₂ := b1e116 (M.op X0 X1) X2 (M.op X3 X4)
           grind)
        | exact superpose b1e116 b1e308
        | exact resolve b1e308 b1e116
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e116 b1e308
      have b1e383 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e333 X0 X1 x x
           have i₂ := b1e10 X0 y (M.op x x)
           grind)
        | exact superpose b1e10 b1e333
        | exact resolve b1e333 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e333
      have b1e389 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op X3 X4) (M.op y y)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e340 x x X2 X3 X4
           have i₂ := b1e10 (M.op X3 X4) y (M.op x x)
           grind)
        | exact superpose b1e10 b1e340
        | exact resolve b1e340 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e340
      have b1e428 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e383 X0 X1
           have i₂ := b1e196 X0
           grind)
        | (have i₁ := b1e383 y X1
           have i₂ := b1e196 (M.op y y)
           grind)
        | exact superpose b1e196 b1e383
        | exact resolve b1e383 b1e196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e383
      have b1e433 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op y (M.op X3 X4)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e389 X2 X3 X4
           have i₂ := b1e196 (M.op X3 X4)
           grind)
        | exact superpose b1e196 b1e389
        | exact resolve b1e389 b1e196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e196 b1e389
      have b1e464 : ∀ X2 X3 X4 : G, (M.op y (M.op X2 X2)) = (M.op y (M.op X3 X4)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e433 X2 X3 X4
           have i₂ := b1e428 (M.op X2 X2) X3
           grind)
        | exact superpose b1e428 b1e433
        | exact resolve b1e433 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e433
      have b1e485 : ∀ X3 X4 : G, (M.op y y) = (M.op y (M.op X3 X4)) := by
        intro X3 X4
        first
        | (have i₁ := b1e464 x X3 X4
           have i₂ := b1e428 y x
           grind)
        | exact superpose b1e428 b1e464
        | exact resolve b1e464 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e464
      have b1e568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b1e54 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e569 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e568
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e568
        | exact resolve b1e568 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e568
      have b1e570 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e569
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e569
        | exact resolve b1e569 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e569
      have b1e571 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e570
           grind)
        | exact superpose b1e570 b1e16
        | exact resolve b1e16 b1e570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e575 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) (σ x))) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 (σ x) (σ y)
           have i₂ := b1e570
           grind)
        | exact superpose b1e570 b1e10
        | exact resolve b1e10 b1e570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e576 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op y (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b1e575 X0
           have i₂ := b1e41 (σ x) X0
           grind)
        | exact superpose b1e41 b1e575
        | exact resolve b1e575 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41 b1e575
      have b1e580 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e576 X0
           have i₂ := b1e10 X0 y (σ x)
           grind)
        | exact superpose b1e10 b1e576
        | exact resolve b1e576 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e576
      have b1e584 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e580 X0
           have i₂ := b1e428 X0 y
           grind)
        | exact superpose b1e428 b1e580
        | exact resolve b1e580 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e580
      have b1e702 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ x))) = (M.op (M.op X0 X1) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e37 X0 X1 (σ x) (σ y)
           have i₂ := b1e570
           grind)
        | exact superpose b1e570 b1e37
        | exact resolve b1e37 b1e570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e570
      have b1e786 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e32 X0 X0 (M.op X2 X2) X4
           have i₂ := b1e37 X0 X1 X2 X3
           grind)
        | (have i₁ := b1e32 X0 X1 (M.op X2 X3) X3
           have i₂ := b1e37 X0 X1 X2 X3
           grind)
        | exact superpose b1e37 b1e32
        | exact resolve b1e32 b1e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32 b1e37
      have b1e809 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op y (M.op X0 X4)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e786 X0 X1 X2 X3 X4
           have i₂ := b1e428 (M.op X0 X4) X2
           grind)
        | exact superpose b1e428 b1e786
        | exact resolve b1e786 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e786
      have b1e859 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e702 X0 x
           have i₂ := b1e160 X0 x (σ x)
           grind)
        | exact superpose b1e160 b1e702
        | exact resolve b1e702 b1e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e160 b1e702
      have b1e894 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op y y) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e809 X0 X1 X2 X3 x
           have i₂ := b1e485 X0 x
           grind)
        | exact superpose b1e485 b1e809
        | exact resolve b1e809 b1e485
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e485 b1e809
      have b1e931 : ∀ X0 : G, (M.op y (σ x)) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) := by
        intro X0
        first
        | (have i₁ := b1e859 X0
           have i₂ := b1e428 (σ x) y
           grind)
        | exact superpose b1e428 b1e859
        | exact resolve b1e859 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e428 b1e859
      have b1e976 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e931 x
           have i₂ := b1e894 x x (σ x) (σ x)
           grind)
        | exact superpose b1e894 b1e931
        | exact resolve b1e931 b1e894
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e894 b1e931
      have b1e1013 : (σ x) = (k (σ x) (M.op y (σ x))) := by grind
      have b1e1036 : (σ x) = (k (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e1013
           have i₂ := b1e976
           grind)
        | exact superpose b1e976 b1e1013
        | exact resolve b1e1013 b1e976
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1013
      have b1e4490 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e55 x x
           grind)
        | exact superpose b1e55 b1e18
        | (have j1 := b1e55 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e55 x y
           grind)
        | exact resolve b1e18 b1e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e4603 : (σ x) = (M.op y (σ x)) ∨ (σ y) ≠ (σ (k x x)) := by
        first
        | (have i₁ := b1e4490
           have i₂ := b1e584 (σ x)
           grind)
        | exact superpose b1e584 b1e4490
        | exact resolve b1e4490 b1e584
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e584 b1e4490
      have b1e4654 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y y) := by
        first
        | (have i₁ := b1e4603
           have i₂ := b1e976
           grind)
        | exact superpose b1e976 b1e4603
        | exact resolve b1e4603 b1e976
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e976 b1e4603
      have b1e7045 : (k x (τ (M.op y y))) = (τ (σ x)) := by
        first
        | (have i₁ := b1e93 x (M.op y y)
           have i₂ := b1e1036
           grind)
        | exact superpose b1e1036 b1e93
        | exact resolve b1e93 b1e1036
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e93 b1e1036
      have b1e7066 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e7045
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e7045
        | exact resolve b1e7045 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7045
      have b1e7124 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e203 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e203
        | (have j0 := b1e203 x x
           grind)
        | exact resolve b1e203 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e203
      have b1e16750 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e4654
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e4654
        | (have j1 := b1e14 y (σ x)
           grind)
        | exact resolve b1e4654 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4654
      have b1e16751 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e16750
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16750
        | exact resolve b1e16750 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16750
      have b1e16752 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
      clear b1e16751
      have b1e16761 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b1e16752
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16752
        | exact resolve b1e16752 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16752
      have b1e16772 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e7066
           have i₂ := b1e16761
           grind)
        | exact superpose b1e16761 b1e7066
        | exact resolve b1e7066 b1e16761
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7066 b1e16761
      have b1e16880 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e16772
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e16772
        | exact resolve b1e16772 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16772
      have b1e16904 : x = (k x x) := by
        first
        | (have r₁ := b1e16880
           have r₂ := b1e7124
           grind)
        | exact resolve b1e16880 b1e7124
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7124 b1e16880
      have b1e16996 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e16904
           grind)
        | exact superpose b1e16904 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e16904
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16904
      have b1e16997 : x = (M.op x x) := by grind
      clear b1e16996
      have b1e17447 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e16997
           grind)
        | exact superpose b1e16997 b1e17
        | exact resolve b1e17 b1e16997
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16997
      have b1e18278 : (σ x) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e571
           have i₂ := b1e17447
           grind)
        | exact superpose b1e17447 b1e571
        | exact resolve b1e571 b1e17447
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e571
      have b1e18304 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b1e18278
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e18278
        | exact resolve b1e18278 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18278
      have b1e18336 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b1e18304
           have i₂ := b1e17447
           grind)
        | exact superpose b1e17447 b1e18304
        | exact resolve b1e18304 b1e17447
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17447 b1e18304
      have b1e18337 : False := by grind
      exact b1e18337
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b2e52 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
      have b2e58 : x = (M.op x y) ∨ y = (M.op x x) := by
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
      have b2e61 : x = (M.op x y) := by
        first
        | (have r₁ := b2e58
           have r₂ := b2e17
           grind)
        | exact resolve b2e58 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e4569 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e57 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e57
        | exact resolve b2e57 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e8967 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e4569
           grind)
        | exact superpose b2e4569 b2e11
        | exact resolve b2e11 b2e4569
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e4569
      have b2e8984 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e8967
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e8967
        | exact resolve b2e8967 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8967
      have b2e8998 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e52 x x
           have i₂ := b2e8984
           grind)
        | exact superpose b2e8984 b2e52
        | exact resolve b2e52 b2e8984
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52 b2e8984
      have b2e9001 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e8998
           have r₂ := b2e17
           grind)
        | exact resolve b2e8998 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e8998
      have b2e9529 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e9001
           grind)
        | exact superpose b2e9001 b2e11
        | exact resolve b2e11 b2e9001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9001
      have b2e9545 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e9529
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e9529
        | exact resolve b2e9529 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9529
      have b2e9546 : x = y := by grind
      clear b2e9545
      have b2e9668 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e9546
           grind)
        | exact superpose b2e9546 b2e16
        | exact resolve b2e16 b2e9546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e9675 : x = (M.op x x) := by
        first
        | (have i₁ := b2e61
           have i₂ := b2e9546
           grind)
        | exact superpose b2e9546 b2e61
        | exact resolve b2e61 b2e9546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e9685 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e9668
           have i₂ := b2e9675
           grind)
        | exact superpose b2e9675 b2e9668
        | exact resolve b2e9668 b2e9675
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9668 b2e9675
      have b2e9688 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e9685
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e9685
        | exact resolve b2e9685 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9685
      have b2e9690 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e9688
           have i₂ := b2e9546
           grind)
        | exact superpose b2e9546 b2e9688
        | exact resolve b2e9688 b2e9546
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9546 b2e9688
      have b2e9691 : False := by grind
      exact b2e9691
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
      have b3e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
      have b3e201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b3e46 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e46
      have b3e202 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e201
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e201
        | exact resolve b3e201 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201
      have b3e256 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e202
           grind)
        | exact superpose b3e202 b3e16
        | exact resolve b3e16 b3e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e202
      have b3e366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
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
      have b3e367 : y = (M.op x x) := by grind
      clear b3e366
      have b3e370 : False := by grind
      exact b3e370

/-- `Equation4485`: `x ◇ (y ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4485 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4485 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
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
      have b0e33 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (σ x) X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 x X1
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 X0 X3
           have i₂ := b0e10 X2 X0 X1
           grind)
        | (have i₁ := b0e10 (M.op X1 X2) X1 X2
           have i₂ := b0e10 (M.op X1 X1) X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X3 X2 (M.op X0 X0)
           have i₂ := b0e10 X2 X0 X1
           grind)
        | (have i₁ := b0e10 X0 (M.op X1 X2) X0
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
      have b0e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X0 X0) X2 X3
           have i₂ := b0e10 (M.op X2 X3) X0 X1
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e10 X0 X1 X2
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X0))) := by
        intro X0 X1
        grind
      have b0e45 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X1 X0 y
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e10 X0 y X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e10
        | exact resolve b0e10 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 (M.op X1 X1) X1 X2
           have i₂ := b0e14 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e14 X0 (M.op X0 (M.op X1 X1))
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 (M.op X1 X1) X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b0e123 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op y (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e33 X0 y
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e33
        | exact resolve b0e33 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e146 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e123 X0
           have i₂ := b0e10 X0 y (σ x)
           grind)
        | exact superpose b0e10 b0e123
        | exact resolve b0e123 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123
      have b0e196 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ y) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 X0 X1 X2 (σ y)
           have i₂ := b0e39 X0
           grind)
        | (have i₁ := b0e35 (σ y) X1 X2 X0
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e35
        | exact resolve b0e35 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e197 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e35 X0 X1 X2 y
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e35 y X1 X2 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e35
        | exact resolve b0e35 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e205 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 x X0 X1 x
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e35
        | exact resolve b0e35 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e248 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e196 X0 X1 X2
           have i₂ := b0e197 (σ y) X0 X2
           grind)
        | exact superpose b0e197 b0e196
        | exact resolve b0e196 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e196
      have b0e261 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op y y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e248 X0 X1 X2
           have i₂ := b0e10 X2 y (σ y)
           grind)
        | exact superpose b0e10 b0e248
        | exact resolve b0e248 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e248
      have b0e270 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (σ y)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e261 X0 X1 X2
           have i₂ := b0e146 X2
           grind)
        | exact superpose b0e146 b0e261
        | exact resolve b0e261 b0e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e261
      have b0e277 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e205 (M.op X0 X0) X2
           have i₂ := b0e10 x X0 X1
           grind)
        | exact superpose b0e10 b0e205
        | exact resolve b0e205 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e205
      have b0e308 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e277 X0 X1 X2
           have i₂ := b0e197 (M.op X0 X1) x X2
           grind)
        | exact superpose b0e197 b0e277
        | exact resolve b0e277 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e277
      have b0e310 : ∀ X2 : G, (M.op X2 (M.op y y)) = (M.op y X2) := by
        intro X2
        first
        | (have i₁ := b0e308 x x X2
           have i₂ := b0e10 X2 y (M.op x x)
           grind)
        | exact superpose b0e10 b0e308
        | exact resolve b0e308 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e308
      have b0e319 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e55 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e347 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y x) X0) := by
        intro X0
        first
        | (have i₁ := b0e34 X0 (M.op y y)
           have i₂ := b0e310 x
           grind)
        | exact superpose b0e310 b0e34
        | exact resolve b0e34 b0e310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e348 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e347 X0
           have i₂ := b0e270 y x X0
           grind)
        | exact superpose b0e270 b0e347
        | exact resolve b0e347 b0e270
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e347
      have b0e490 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X2 X3) (M.op X2 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X0 (M.op X2 X3) X1
           have i₂ := b0e37 X2 X3 X1 X0
           grind)
        | (have i₁ := b0e10 (M.op X2 X2) X1 X2
           have i₂ := b0e37 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact superpose b0e37 b0e10
        | exact resolve b0e10 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e511 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y (M.op X2 X3)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e490 X0 X1 X2 X3
           have i₂ := b0e45 (M.op X2 X3) X0
           grind)
        | exact superpose b0e45 b0e490
        | exact resolve b0e490 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e490
      have b0e570 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e511 X0 X1 x x
           have i₂ := b0e10 X0 y (M.op x x)
           grind)
        | exact superpose b0e10 b0e511
        | exact resolve b0e511 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511
      have b0e623 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e570 X0 X1
           have i₂ := b0e146 X0
           grind)
        | exact superpose b0e146 b0e570
        | exact resolve b0e570 b0e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146 b0e570
      have b0e668 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e623 X0 X1
           have i₂ := b0e348 X0
           grind)
        | exact superpose b0e348 b0e623
        | exact resolve b0e623 b0e348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e623
      have b0e787 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e39 X0
           have i₂ := b0e348 X0
           grind)
        | exact superpose b0e348 b0e39
        | exact resolve b0e39 b0e348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e803 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e348 (σ x)
           grind)
        | exact superpose b0e348 b0e16
        | exact resolve b0e16 b0e348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e808 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e803
           have i₂ := b0e40 (σ x)
           grind)
        | exact superpose b0e40 b0e803
        | exact resolve b0e803 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e803
      have b0e2997 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e668 X0 X1
           grind)
        | exact superpose b0e668 b0e10
        | exact resolve b0e10 b0e668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e60 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60
      have b0e9187 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e43 X1 X2
           have i₂ := b0e57 X0 X1 X2
           grind)
        | (have i₁ := b0e43 X0 X1
           have i₂ := b0e57 (M.op (M.op X0 X1) (M.op X0 X0)) X1 X2
           grind)
        | exact superpose b0e57 b0e43
        | (have j1 := b0e57 X0 X1 X2
           grind)
        | exact resolve b0e43 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e9234 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X3 X3)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e41 (M.op X1 X2) (M.op X1 X1) X3 X4
           have i₂ := b0e57 X0 X1 X2
           grind)
        | (have i₁ := b0e41 X0 X1 X2 X3
           have i₂ := b0e57 (M.op X0 X1) X1 X2
           grind)
        | exact superpose b0e57 b0e41
        | (have j1 := b0e57 X0 X1 X2
           grind)
        | exact resolve b0e41 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e57
      have b0e9260 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y (M.op X1 X2)) (M.op X3 X3)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e9234 X0 X1 X2 X3 X4
           have i₂ := b0e197 (M.op X1 X2) (M.op X1 X2) (M.op X3 X3)
           grind)
        | exact superpose b0e197 b0e9234
        | (have j0 := b0e9234 X0 X1 X2 X3 X4
           grind)
        | exact resolve b0e9234 b0e197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e197 b0e9234
      have b0e9298 : ∀ X0 X1 X2 : G, (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e9187 X0 X1 X2
           have i₂ := b0e668 X0 X1
           grind)
        | exact superpose b0e668 b0e9187
        | (have j0 := b0e9187 X0 X1 X2
           grind)
        | exact resolve b0e9187 b0e668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9187
      have b0e9403 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X3 X3) (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9260 X0 X1 x X3 X4
           have i₂ := b0e10 (M.op X3 X3) y (M.op X1 x)
           grind)
        | exact superpose b0e10 b0e9260
        | (have j0 := b0e9260 X0 X1 x X3 X4
           grind)
        | exact resolve b0e9260 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9260
      have b0e9537 : ∀ X0 X1 X3 X4 : G, (M.op (M.op y y) (σ y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9403 X0 X1 X3 X4
           have i₂ := b0e270 X3 X3 (M.op y y)
           grind)
        | exact superpose b0e270 b0e9403
        | (have j0 := b0e9403 X0 X1 X3 X4
           grind)
        | exact resolve b0e9403 b0e270
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9403
      have b0e9655 : ∀ X0 X1 X3 X4 : G, (M.op (σ y) (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9537 X0 X1 X3 X4
           have i₂ := b0e10 (σ y) y y
           grind)
        | exact superpose b0e10 b0e9537
        | (have j0 := b0e9537 X0 X1 X3 X4
           grind)
        | exact resolve b0e9537 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9537
      have b0e9759 : ∀ X0 X1 X3 X4 : G, (M.op (M.op y y) y) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9655 X0 X1 X3 X4
           have i₂ := b0e787 (M.op y y)
           grind)
        | exact superpose b0e787 b0e9655
        | (have j0 := b0e9655 X0 X1 X3 X4
           grind)
        | exact resolve b0e9655 b0e787
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9655
      have b0e9858 : ∀ X0 X1 X3 X4 : G, (M.op y (M.op y y)) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9759 X0 X1 X3 X4
           have i₂ := b0e10 y y y
           grind)
        | exact superpose b0e10 b0e9759
        | (have j0 := b0e9759 X0 X1 X3 X4
           grind)
        | exact resolve b0e9759 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9759
      have b0e9942 : ∀ X0 X1 X3 X4 : G, (M.op y y) = (M.op X0 (M.op X3 X4)) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9858 X0 X1 X3 X4
           have i₂ := b0e668 y y
           grind)
        | exact superpose b0e668 b0e9858
        | (have j0 := b0e9858 X0 X1 X3 X4
           grind)
        | exact resolve b0e9858 b0e668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9858
      have b0e10016 : ∀ X0 X1 X3 X4 : G, (M.op X0 y) = (k (M.op X1 X1) X0) ∨ (M.op y y) = (M.op X0 (M.op X3 X4)) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e9942 X0 X1 X3 X4
           have i₂ := b0e668 X0 X1
           grind)
        | exact superpose b0e668 b0e9942
        | (have j0 := b0e9942 X0 X1 X3 X4
           grind)
        | exact resolve b0e9942 b0e668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9942
      have b0e12360 : ∀ X0 X1 X2 : G, (M.op X0 y) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e319 X0 (M.op X1 X2)
           have i₂ := b0e2997 X0 X1 X2
           grind)
        | exact superpose b0e2997 b0e319
        | (have j0 := b0e319 X0 (M.op X1 X2)
           grind)
        | exact resolve b0e319 b0e2997
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e319
      have b0e29392 : ∀ X0 X1 X2 : G, (M.op y X0) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e12360 X0 X1 X2
           have i₂ := b0e40 X0
           grind)
        | (have i₁ := b0e12360 y X1 X2
           have i₂ := b0e40 y
           grind)
        | exact superpose b0e40 b0e12360
        | (have j0 := b0e12360 X0 X1 X2
           grind)
        | exact resolve b0e12360 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12360
      have b0e29565 : ∀ X0 X1 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29392 (M.op y y) X0 X1
           have i₂ := b0e310 y
           grind)
        | exact superpose b0e310 b0e29392
        | (have j0 := b0e29392 (M.op y y) X0 X1
           grind)
        | (have r₁ := b0e29392 (M.op y y) X1 x
           have r₂ := b0e310 y
           grind)
        | exact resolve b0e29392 b0e310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e310 b0e29392
      have b0e29571 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e29565 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29565
      have b0e45192 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e8711 (M.op y y)
           have i₂ := b0e29571 y y
           grind)
        | exact superpose b0e29571 b0e8711
        | (have j0 := b0e8711 (M.op y y)
           grind)
        | exact resolve b0e8711 b0e29571
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8711 b0e29571
      have b0e45204 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
      clear b0e45192
      have b0e77130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 y) ∨ (M.op X1 y) = (k (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e9298 X1 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9298
      have b0e79563 : ∀ X0 X2 : G, (M.op X0 y) = (k (M.op X2 X2) X0) ∨ (M.op X0 y) = (M.op y y) := by
        intro X0 X2
        first
        | (have i₁ := b0e668 X0 x
           have i₂ := b0e10016 X0 X2 x x
           grind)
        | exact superpose b0e10016 b0e668
        | (have j1 := b0e10016 X0 X2 x x
           grind)
        | exact resolve b0e668 b0e10016
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10016
      have b0e172784 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e668 X0 (σ (M.op y y))
           have i₂ := b0e45204
           grind)
        | exact superpose b0e45204 b0e668
        | exact resolve b0e668 b0e45204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e668
      have b0e172839 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e2997 X0 (σ (M.op y y)) (σ (M.op y y))
           have i₂ := b0e45204
           grind)
        | exact superpose b0e45204 b0e2997
        | exact resolve b0e2997 b0e45204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2997
      have b0e173372 : (σ (M.op y y)) = (M.op (σ (M.op y y)) y) := by
        first
        | (have i₁ := b0e45204
           have i₂ := b0e172784 (σ (M.op y y))
           grind)
        | exact superpose b0e172784 b0e45204
        | exact resolve b0e45204 b0e172784
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45204 b0e172784
      have b0e173433 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e173372
           have i₂ := b0e172839 y
           grind)
        | exact superpose b0e172839 b0e173372
        | exact resolve b0e173372 b0e172839
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e172839 b0e173372
      have b0e174412 : ∀ X0 : G, (k (M.op y y) (σ X0)) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 (M.op y y) X0
           have i₂ := b0e173433
           grind)
        | exact superpose b0e173433 b0e15
        | exact resolve b0e15 b0e173433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e173433
      have b0e186655 : ∀ X0 X1 X2 : G, (M.op X2 y) ≠ (M.op (M.op X0 X1) (σ y)) ∨ (M.op X2 y) = (k (M.op (M.op X0 X1) (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e77130 (M.op X0 X1) X1
           have i₂ := b0e270 X0 X1 (M.op X0 X1)
           grind)
        | exact superpose b0e270 b0e77130
        | exact resolve b0e77130 b0e270
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77130
      have b0e186731 : ∀ X0 X1 X2 : G, (M.op X2 y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X2 y) = (k (M.op (M.op X0 X1) (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e186655 X0 X1 X2
           have i₂ := b0e270 X0 X1 (σ y)
           grind)
        | exact superpose b0e270 b0e186655
        | (have j0 := b0e186655 X0 X1 X2
           grind)
        | exact resolve b0e186655 b0e270
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186655
      have b0e186786 : ∀ X0 X1 X2 : G, (M.op X2 y) ≠ (M.op (σ y) y) ∨ (M.op X2 y) = (k (M.op (M.op X0 X1) (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e186731 X0 X1 X2
           have i₂ := b0e787 (σ y)
           grind)
        | exact superpose b0e787 b0e186731
        | (have j0 := b0e186731 X0 X1 X2
           grind)
        | (have r₁ := b0e186731 X0 X1 (σ y)
           have r₂ := b0e787 (σ y)
           grind)
        | exact resolve b0e186731 b0e787
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186731
      have b0e186831 : ∀ X0 X1 X2 : G, (M.op X2 y) ≠ (M.op y (σ y)) ∨ (M.op X2 y) = (k (M.op (M.op X0 X1) (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e186786 X0 X1 X2
           have i₂ := b0e39 y
           grind)
        | exact superpose b0e39 b0e186786
        | (have j0 := b0e186786 X0 X1 X2
           grind)
        | exact resolve b0e186786 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186786
      have b0e186868 : ∀ X0 X1 X2 : G, (M.op y y) ≠ (M.op X2 y) ∨ (M.op X2 y) = (k (M.op (M.op X0 X1) (σ y)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e186831 X0 X1 X2
           have i₂ := b0e348 y
           grind)
        | exact superpose b0e348 b0e186831
        | (have j0 := b0e186831 X0 X1 X2
           grind)
        | (have r₁ := b0e186831 X0 X1 y
           have r₂ := b0e348 y
           grind)
        | exact resolve b0e186831 b0e348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186831
      have b0e186893 : ∀ X2 : G, (M.op X2 y) = (k (M.op (σ y) (σ y)) X2) ∨ (M.op y y) ≠ (M.op X2 y) := by
        intro X2
        first
        | (have i₁ := b0e186868 x x X2
           have i₂ := b0e270 x x (σ y)
           grind)
        | exact superpose b0e270 b0e186868
        | (have j0 := b0e186868 x x X2
           grind)
        | exact resolve b0e186868 b0e270
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e270 b0e186868
      have b0e186914 : ∀ X2 : G, (M.op X2 y) = (k (M.op (σ y) (σ y)) X2) := by
        intro X2
        first
        | (have j0 := b0e186893 X2
           have j1 := b0e79563 X2 (σ y)
           grind)
        | (have r₁ := b0e186893 y
           have r₂ := b0e79563 y X2
           grind)
        | (have r₁ := b0e186893 x
           have r₂ := b0e79563 x X2
           grind)
        | exact resolve b0e186893 b0e79563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79563 b0e186893
      have b0e186935 : ∀ X2 : G, (M.op X2 y) = (k (M.op (σ y) y) X2) := by
        intro X2
        first
        | (have i₁ := b0e186914 X2
           have i₂ := b0e787 (σ y)
           grind)
        | exact superpose b0e787 b0e186914
        | exact resolve b0e186914 b0e787
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e787 b0e186914
      have b0e186956 : ∀ X2 : G, (M.op X2 y) = (k (M.op y (σ y)) X2) := by
        intro X2
        first
        | (have i₁ := b0e186935 X2
           have i₂ := b0e39 y
           grind)
        | exact superpose b0e39 b0e186935
        | exact resolve b0e186935 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e186935
      have b0e186977 : ∀ X2 : G, (M.op X2 y) = (k (M.op y y) X2) := by
        intro X2
        first
        | (have i₁ := b0e186956 X2
           have i₂ := b0e348 y
           grind)
        | exact superpose b0e348 b0e186956
        | exact resolve b0e186956 b0e348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e348 b0e186956
      have b0e187111 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (M.op y y) X0)) := by
        intro X0
        first
        | (have i₁ := b0e174412 X0
           have i₂ := b0e186977 (σ X0)
           grind)
        | exact superpose b0e186977 b0e174412
        | exact resolve b0e174412 b0e186977
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e174412
      have b0e187236 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e187111 X0
           have i₂ := b0e186977 X0
           grind)
        | exact superpose b0e186977 b0e187111
        | exact resolve b0e187111 b0e186977
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186977 b0e187111
      have b0e187276 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e187236 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e187236
        | exact resolve b0e187236 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e187236
      have b0e191040 : (M.op y (σ x)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e808
           have i₂ := b0e187276 x
           grind)
        | exact superpose b0e187276 b0e808
        | (have r₁ := b0e808
           have r₂ := b0e187276 x
           grind)
        | exact resolve b0e808 b0e187276
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e808 b0e187276
      have b0e191084 : False := by grind
      exact b0e191084
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 X0 X3
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e10 (M.op X1 X2) X1 X2
           have i₂ := b1e10 (M.op X1 X1) X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
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
      have b1e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X3 X2 (M.op X0 X0)
           have i₂ := b1e10 X2 X0 X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X2) X0
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e41 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X1 X0 y
           have i₂ := b1e34 X0
           grind)
        | (have i₁ := b1e10 X0 y X0
           have i₂ := b1e34 X0
           grind)
        | exact superpose b1e34 b1e10
        | exact resolve b1e10 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b1e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b1e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b1e91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 X0 X1 X2 y
           have i₂ := b1e34 X0
           grind)
        | (have i₁ := b1e32 y X1 X2 X0
           have i₂ := b1e34 X0
           grind)
        | exact superpose b1e34 b1e32
        | exact resolve b1e32 b1e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e120 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e32 x X0 X1 x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e32
        | exact resolve b1e32 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e162 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e120 (M.op X0 X0) X2
           have i₂ := b1e10 x X0 X1
           grind)
        | exact superpose b1e10 b1e120
        | exact resolve b1e120 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e120
      have b1e191 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (M.op y (M.op X0 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e162 X0 X1 X2
           have i₂ := b1e114 (M.op X0 X1) x X2
           grind)
        | exact superpose b1e114 b1e162
        | exact resolve b1e162 b1e114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e114 b1e162
      have b1e192 : ∀ X2 : G, (M.op y X2) = (M.op X2 (M.op y y)) := by
        intro X2
        first
        | (have i₁ := b1e191 x x X2
           have i₂ := b1e10 X2 y (M.op x x)
           grind)
        | exact superpose b1e10 b1e191
        | exact resolve b1e191 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e191
      have b1e199 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e50 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50
      have b1e312 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op (M.op X2 X3) (M.op X2 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 (M.op X2 X3) X1
           have i₂ := b1e35 X2 X3 X1 X0
           grind)
        | (have i₁ := b1e10 (M.op X2 X2) X1 X2
           have i₂ := b1e35 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact superpose b1e35 b1e10
        | exact resolve b1e10 b1e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35
      have b1e329 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op y (M.op X2 X3)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e312 X0 X1 X2 X3
           have i₂ := b1e41 (M.op X2 X3) X0
           grind)
        | exact superpose b1e41 b1e312
        | exact resolve b1e312 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e312
      have b1e379 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e329 X0 X1 x x
           have i₂ := b1e10 X0 y (M.op x x)
           grind)
        | exact superpose b1e10 b1e329
        | exact resolve b1e329 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e329
      have b1e424 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e379 X0 X1
           have i₂ := b1e192 X0
           grind)
        | (have i₁ := b1e379 y X1
           have i₂ := b1e192 (M.op y y)
           grind)
        | exact superpose b1e192 b1e379
        | exact resolve b1e379 b1e192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e192 b1e379
      have b1e560 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b1e54 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e54
      have b1e561 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e560
           have i₂ := b1e15 x y
           grind)
        | exact superpose b1e15 b1e560
        | exact resolve b1e560 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e560
      have b1e562 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e561
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e561
        | exact resolve b1e561 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e561
      have b1e566 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ y) (σ y))) := by
        intro X0
        first
        | (have i₁ := b1e10 X0 (σ y) (σ x)
           have i₂ := b1e562
           grind)
        | exact superpose b1e562 b1e10
        | exact resolve b1e10 b1e562
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e567 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op y (σ y)) X0) := by
        intro X0
        first
        | (have i₁ := b1e566 X0
           have i₂ := b1e41 (σ y) X0
           grind)
        | exact superpose b1e41 b1e566
        | exact resolve b1e566 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41 b1e566
      have b1e571 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e567 X0
           have i₂ := b1e10 X0 y (σ y)
           grind)
        | exact superpose b1e10 b1e567
        | exact resolve b1e567 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e567
      have b1e575 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e571 X0
           have i₂ := b1e424 X0 y
           grind)
        | exact superpose b1e424 b1e571
        | exact resolve b1e571 b1e424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e571
      have b1e677 : (σ y) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e575 (σ x)
           grind)
        | exact superpose b1e575 b1e18
        | exact resolve b1e18 b1e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e681 : (σ x) = (k (σ x) (M.op y (σ x))) := by grind
      have b1e692 : (M.op y y) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e34 (σ x)
           have i₂ := b1e575 y
           grind)
        | exact superpose b1e575 b1e34
        | exact resolve b1e34 b1e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e700 : (σ x) = (k (σ x) (M.op y y)) := by
        first
        | (have i₁ := b1e681
           have i₂ := b1e692
           grind)
        | exact superpose b1e692 b1e681
        | exact resolve b1e681 b1e692
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e681
      have b1e703 : (σ y) ≠ (M.op y y) := by
        first
        | (have i₁ := b1e677
           have i₂ := b1e692
           grind)
        | exact superpose b1e692 b1e677
        | exact resolve b1e677 b1e692
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e677
      have b1e1419 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op y X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X0 X1 X2
           have i₂ := b1e424 X0 X1
           grind)
        | exact superpose b1e424 b1e10
        | exact resolve b1e10 b1e424
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e424
      have b1e4780 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e55 x x
           grind)
        | exact superpose b1e55 b1e18
        | (have j1 := b1e55 x x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e55 y x
           grind)
        | exact resolve b1e18 b1e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e55
      have b1e4891 : (σ x) = (M.op y (σ x)) ∨ (σ y) ≠ (σ (k x x)) := by
        first
        | (have i₁ := b1e4780
           have i₂ := b1e575 (σ x)
           grind)
        | exact superpose b1e575 b1e4780
        | exact resolve b1e4780 b1e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4780
      have b1e4938 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y y) := by
        first
        | (have i₁ := b1e4891
           have i₂ := b1e692
           grind)
        | exact superpose b1e692 b1e4891
        | exact resolve b1e4891 b1e692
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4891
      have b1e6611 : (k x (τ (M.op y y))) = (τ (σ x)) := by
        first
        | (have i₁ := b1e91 x (M.op y y)
           have i₂ := b1e700
           grind)
        | exact superpose b1e700 b1e91
        | exact resolve b1e91 b1e700
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e91 b1e700
      have b1e6632 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e6611
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e6611
        | exact resolve b1e6611 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6611
      have b1e6688 : x ≠ y ∨ x = (k x x) := by
        first
        | (have i₁ := b1e199 x x
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e199
        | (have j0 := b1e199 x x
           grind)
        | exact resolve b1e199 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e199
      have b1e16295 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e4938
           have i₂ := b1e14 x x
           grind)
        | exact superpose b1e14 b1e4938
        | (have j1 := b1e14 y (σ x)
           grind)
        | exact resolve b1e4938 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4938
      have b1e16296 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e16295
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16295
        | exact resolve b1e16295 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16295
      have b1e16297 : (σ x) = (M.op y y) ∨ x = (M.op x x) := by grind
      clear b1e16296
      have b1e16306 : (σ x) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b1e16297
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16297
        | exact resolve b1e16297 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16297
      have b1e16317 : x = (k x (τ (σ x))) ∨ x = y := by
        first
        | (have i₁ := b1e6632
           have i₂ := b1e16306
           grind)
        | exact superpose b1e16306 b1e6632
        | exact resolve b1e6632 b1e16306
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6632 b1e16306
      have b1e16422 : x = (k x x) ∨ x = y := by
        first
        | (have i₁ := b1e16317
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e16317
        | exact resolve b1e16317 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16317
      have b1e16446 : x = (k x x) := by
        first
        | (have r₁ := b1e16422
           have r₂ := b1e6688
           grind)
        | exact resolve b1e16422 b1e6688
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e6688 b1e16422
      have b1e16914 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e16446
           grind)
        | exact superpose b1e16446 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e16446
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16446
      have b1e16919 : x = (M.op x x) := by grind
      clear b1e16914
      have b1e17102 : x = y := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e16919
           grind)
        | exact superpose b1e16919 b1e17
        | exact resolve b1e17 b1e16919
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e17156 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b1e1419 X0 x x
           have i₂ := b1e16919
           grind)
        | exact superpose b1e16919 b1e1419
        | exact resolve b1e1419 b1e16919
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1419 b1e16919
      have b1e18022 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b1e562
           have i₂ := b1e17102
           grind)
        | exact superpose b1e17102 b1e562
        | exact resolve b1e562 b1e17102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e562
      have b1e18024 : (M.op x x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e692
           have i₂ := b1e17102
           grind)
        | exact superpose b1e17102 b1e692
        | exact resolve b1e692 b1e17102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e692
      have b1e18026 : (σ x) ≠ (M.op x x) := by
        first
        | (have i₁ := b1e703
           have i₂ := b1e17102
           grind)
        | exact superpose b1e17102 b1e703
        | exact resolve b1e703 b1e17102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e703
      have b1e18038 : y ≠ (σ x) := by
        first
        | (have i₁ := b1e18026
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e18026
        | exact resolve b1e18026 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18026
      have b1e18040 : y = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e18024
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e18024
        | exact resolve b1e18024 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18024
      have b1e18042 : (σ x) = (M.op y (σ x)) := by
        first
        | (have i₁ := b1e18022
           have i₂ := b1e575 (σ x)
           grind)
        | exact superpose b1e575 b1e18022
        | exact resolve b1e18022 b1e575
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e575 b1e18022
      have b1e18068 : x ≠ (σ x) := by
        first
        | (have i₁ := b1e18038
           have i₂ := b1e17102
           grind)
        | exact superpose b1e17102 b1e18038
        | exact resolve b1e18038 b1e17102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18038
      have b1e18070 : x = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e18040
           have i₂ := b1e17102
           grind)
        | exact superpose b1e17102 b1e18040
        | exact resolve b1e18040 b1e17102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17102 b1e18040
      have b1e18072 : (σ x) = (M.op x (σ x)) := by
        first
        | (have i₁ := b1e18042
           have i₂ := b1e17156 (σ x)
           grind)
        | exact superpose b1e17156 b1e18042
        | exact resolve b1e18042 b1e17156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17156 b1e18042
      have b1e18079 : x = (σ x) := by
        first
        | (have i₁ := b1e18072
           have i₂ := b1e18070
           grind)
        | exact superpose b1e18070 b1e18072
        | exact resolve b1e18072 b1e18070
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18070 b1e18072
      have b1e18081 : False := by grind
      exact b1e18081
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b2e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b2e58 : x = (M.op y x) ∨ y = (M.op x x) := by
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
      have b2e61 : x = (M.op y x) := by
        first
        | (have r₁ := b2e58
           have r₂ := b2e17
           grind)
        | exact resolve b2e58 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58
      have b2e9078 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e57 x x
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e57
        | exact resolve b2e57 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e57
      have b2e18689 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e11 (k x x)
           have i₂ := b2e9078
           grind)
        | exact superpose b2e9078 b2e11
        | exact resolve b2e11 b2e9078
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e9078
      have b2e18706 : y = (k x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e18689
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e18689
        | exact resolve b2e18689 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18689
      have b2e18720 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e52 x x
           have i₂ := b2e18706
           grind)
        | exact superpose b2e18706 b2e52
        | exact resolve b2e52 b2e18706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52 b2e18706
      have b2e18723 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b2e18720
           have r₂ := b2e17
           grind)
        | exact resolve b2e18720 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18720
      have b2e19264 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e18723
           grind)
        | exact superpose b2e18723 b2e11
        | exact resolve b2e11 b2e18723
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e18723
      have b2e19280 : x = y ∨ x = y := by
        first
        | (have i₁ := b2e19264
           have i₂ := b2e11 x
           grind)
        | exact superpose b2e11 b2e19264
        | exact resolve b2e19264 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19264
      have b2e19281 : x = y := by grind
      clear b2e19280
      have b2e19399 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e19281
           grind)
        | exact superpose b2e19281 b2e16
        | exact resolve b2e16 b2e19281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e19406 : x = (M.op x x) := by
        first
        | (have i₁ := b2e61
           have i₂ := b2e19281
           grind)
        | exact superpose b2e19281 b2e61
        | exact resolve b2e61 b2e19281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61
      have b2e19424 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e19399
           have i₂ := b2e19406
           grind)
        | exact superpose b2e19406 b2e19399
        | exact resolve b2e19399 b2e19406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19399 b2e19406
      have b2e19429 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e19424
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e19424
        | exact resolve b2e19424 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19424
      have b2e19433 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b2e19429
           have i₂ := b2e19281
           grind)
        | exact superpose b2e19281 b2e19429
        | exact resolve b2e19429 b2e19281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19281 b2e19429
      have b2e19434 : False := by grind
      exact b2e19434
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X0) := by
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
      have b3e24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X2 X0 X3
           have i₂ := b3e10 X2 X0 X1
           grind)
        | (have i₁ := b3e10 (M.op X1 X2) X1 X2
           have i₂ := b3e10 (M.op X1 X1) X1 X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e26 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X3 X2 (M.op X0 X0)
           have i₂ := b3e10 X2 X0 X1
           grind)
        | (have i₁ := b3e10 X0 (M.op X1 X2) X0
           have i₂ := b3e10 X0 X1 X2
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e20 X0 X1
           grind)
        | exact superpose b3e20 b3e11
        | exact resolve b3e11 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e41 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) X1) ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e10 X1 X2 X3
           have i₂ := b3e14 X2 X0
           grind)
        | (have i₁ := b3e10 X0 X1 X2
           have i₂ := b3e14 X0 (M.op X1 X1)
           grind)
        | exact superpose b3e14 b3e10
        | (have j1 := b3e14 X2 X0
           grind)
        | exact resolve b3e10 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e46 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
      have b3e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
      have b3e50 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
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
      have b3e55 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b3e68 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 X2 X3 X4 (M.op X0 X0)
           have i₂ := b3e10 X2 X0 X1
           grind)
        | (have i₁ := b3e24 (M.op X1 X2) X1 X2 X0
           have i₂ := b3e10 X0 X1 X2
           grind)
        | exact superpose b3e10 b3e24
        | exact resolve b3e24 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e42 (σ X1) (σ X0)
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e42
        | exact resolve b3e42 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e170 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e24 (M.op X2 X3) X1 X0 X4
           have i₂ := b3e26 X2 X3 X1 X0
           grind)
        | (have i₁ := b3e24 X0 X1 (M.op X2 X2) X3
           have i₂ := b3e26 X0 X1 X2 (M.op X0 X1)
           grind)
        | exact superpose b3e26 b3e24
        | exact resolve b3e24 b3e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24 b3e26
      have b3e183 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b3e55
      have b3e197 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e183 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e183
        | exact resolve b3e183 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e183
      have b3e201 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have j0 := b3e46 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e46
      have b3e202 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e201
           have i₂ := b3e15 x y
           grind)
        | exact superpose b3e15 b3e201
        | exact resolve b3e201 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e201
      have b3e660 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X4 X5) ∨ (k X2 X5) = (M.op X5 X2) ∨ (k X0 X4) = (M.op X4 X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b3e41 X5 X4 X2 X3
           have i₂ := b3e41 X4 (M.op X2 X3) X0 X1
           grind)
        | (have i₁ := b3e41 X0 X1 X2 X3
           have i₂ := b3e41 X0 X1 X2 X3
           grind)
        | exact superpose b3e41 b3e41
        | (have j0 := b3e41 X5 X1 X2 X3
           have j1 := b3e41 X5 X1 X2 X3
           grind)
        | exact resolve b3e41 b3e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e41
      have b3e882 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X4 X5) X0) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b3e68 x x X4 X5 X0
           have i₂ := b3e170 X0 X1 x x X4
           grind)
        | (have i₁ := b3e68 X0 X1 x x (M.op X1 X1)
           have i₂ := b3e170 (M.op (M.op X0 X1) x) X1 x x X4
           grind)
        | exact superpose b3e170 b3e68
        | exact resolve b3e68 b3e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e68 b3e170
      have b3e1207 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e10 X2 X3 X4
           have i₂ := b3e882 X2 X3 X0 X1
           grind)
        | (have i₁ := b3e10 (M.op X4 x) X1 X2
           have i₂ := b3e882 (M.op X1 X1) X1 X4 x
           grind)
        | exact superpose b3e882 b3e10
        | exact resolve b3e10 b3e882
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2574 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e47 X0 X0
           have i₂ := b3e14 (σ X0) X1
           grind)
        | (have i₁ := b3e47 X0 X1
           have i₂ := b3e14 X0 (M.op (σ X0) (σ X1))
           grind)
        | exact superpose b3e14 b3e47
        | (have j1 := b3e14 (σ X1) X0
           grind)
        | exact resolve b3e47 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2632 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 X1
           have i₂ := b3e47 X1 X0
           grind)
        | exact superpose b3e47 b3e11
        | (have j1 := b3e47 X1 X0
           grind)
        | exact resolve b3e11 b3e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e2643 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e197 X1
           have i₂ := b3e47 X0 X1
           grind)
        | exact superpose b3e47 b3e197
        | (have j1 := b3e47 X0 X1
           grind)
        | exact resolve b3e197 b3e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e197
      have b3e2685 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2643 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e2643
        | (have j0 := b3e2643 X0 X1
           grind)
        | exact resolve b3e2643 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2643
      have b3e13524 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e50 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e50
        | exact resolve b3e50 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e50
      have b3e13782 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e13524 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e13524
        | (have j0 := b3e13524 X0 X1
           grind)
        | exact resolve b3e13524 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13524
      have b3e13981 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b3e18764 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e14 (σ X0) X1
           have i₂ := b3e99 X0 X0
           grind)
        | exact superpose b3e99 b3e14
        | (have j0 := b3e14 (σ X0) X1
           have j1 := b3e99 X0 X0
           grind)
        | exact resolve b3e14 b3e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e99
      have b3e44606 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2632 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e2632
        | exact resolve b3e2632 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e44615 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e2632 X1 X1
           have i₂ := b3e47 X0 X1
           grind)
        | exact superpose b3e47 b3e2632
        | (have j0 := b3e2632 X1 X0
           have j1 := b3e47 X0 X1
           grind)
        | exact resolve b3e2632 b3e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e47 b3e2632
      have b3e44794 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e44615 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e44615
        | (have j0 := b3e44615 X0 X1
           grind)
        | exact resolve b3e44615 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44615
      have b3e44795 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e44606 X0 X1
           have i₂ := b3e20 X0 X1
           grind)
        | exact superpose b3e20 b3e44606
        | (have j0 := b3e44606 X0 X1
           grind)
        | exact resolve b3e44606 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44606
      have b3e44987 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (τ (M.op X1 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e35 X1 X0
           have i₂ := b3e44795 X1 X0
           grind)
        | exact superpose b3e44795 b3e35
        | (have j1 := b3e44795 X1 X0
           grind)
        | exact resolve b3e35 b3e44795
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35 b3e44795
      have b3e71122 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e2574 X0 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e2574
        | (have j0 := b3e2574 X1 (τ X0)
           grind)
        | exact resolve b3e2574 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e71275 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e71122 X0 X1
           have i₂ := b3e21 X0 (τ X0)
           grind)
        | exact superpose b3e21 b3e71122
        | (have j0 := b3e71122 X0 X1
           grind)
        | exact resolve b3e71122 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71122
      have b3e71290 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e71275 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e71275
        | (have j0 := b3e71275 X0 X1
           grind)
        | exact resolve b3e71275 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71275
      have b3e96032 : (σ y) ≠ (σ (k x x)) ∨ x = (k x x) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e2685 x x
           grind)
        | exact superpose b3e2685 b3e18
        | (have j1 := b3e2685 x x
           grind)
        | exact resolve b3e18 b3e2685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e96033 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e2685 x y
           grind)
        | exact superpose b3e2685 b3e16
        | (have j1 := b3e2685 x y
           grind)
        | exact resolve b3e16 b3e2685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e96097 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e882 X1 (σ X0) X2 X3
           have i₂ := b3e2685 X0 X0
           grind)
        | exact superpose b3e2685 b3e882
        | (have j1 := b3e2685 X0 X0
           grind)
        | exact resolve b3e882 b3e2685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e96270 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (M.op (σ (k X0 X1)) X4) ∨ (k X0 X1) = X0 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b3e1207 X2 X3 X4 (σ X1) (σ X0)
           have i₂ := b3e2685 X1 X0
           grind)
        | exact superpose b3e2685 b3e1207
        | (have j1 := b3e2685 X1 X0
           grind)
        | exact resolve b3e1207 b3e2685
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2685
      have b3e96340 : y = (k y x) := by
        first
        | (have j1 := b3e13981 x y
           grind)
        | (have r₁ := b3e96033
           have r₂ := b3e13981 x y
           grind)
        | exact resolve b3e96033 b3e13981
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13981 b3e96033
      have b3e98418 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e13782 x y
           have i₂ := b3e96340
           grind)
        | exact superpose b3e96340 b3e13782
        | (have j0 := b3e13782 x y
           grind)
        | exact resolve b3e13782 b3e96340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13782
      have b3e101416 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b3e96032
           have i₂ := b3e71290 x x
           grind)
        | (have i₁ := b3e96032
           have i₂ := b3e71290 X0 (k x x)
           grind)
        | exact superpose b3e71290 b3e96032
        | (have j1 := b3e71290 x X0
           grind)
        | (have r₁ := b3e96032
           have r₂ := b3e71290 (σ y) (σ (k x x))
           grind)
        | (have r₁ := b3e96032
           have r₂ := b3e71290 (σ (k x x)) (σ y)
           grind)
        | exact resolve b3e96032 b3e71290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71290 b3e96032
      have b3e101427 : ∀ X0 : G, (σ X0) ≠ (σ y) ∨ x = X0 ∨ (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b3e101416 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e101416
      have b3e211472 : (k x y) = (M.op y x) ∨ x = y := by
        first
        | (have j0 := b3e101427 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e101427
      have b3e312682 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X3)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b3e660 X0 X2 X0 X3 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e660
      have b3e312683 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X3)) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1 X2 X3
        first
        | (have j0 := b3e312682 X0 X1 X2 X3
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e312682
      have b3e335119 : ∀ X0 : G, (k (τ (σ X0)) X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
        intro X0
        first
        | (have j0 := b3e44987 X0 (σ X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44987
      have b3e335120 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b3e335119 X0
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e335119
        | (have j0 := b3e335119 X0
           grind)
        | exact resolve b3e335119 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e335119
      have b3e687885 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e44794 x y
           grind)
        | exact superpose b3e44794 b3e16
        | (have j1 := b3e44794 x y
           grind)
        | (have r₁ := b3e16
           have r₂ := b3e44794 (σ (M.op x y)) (M.op (σ x) (σ y))
           grind)
        | (have r₁ := b3e16
           have r₂ := b3e44794 (M.op (σ x) (σ y)) (σ (M.op x y))
           grind)
        | exact resolve b3e16 b3e44794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44794
      have b3e687890 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
        first
        | (have i₁ := b3e687885
           have i₂ := b3e96340
           grind)
        | exact superpose b3e96340 b3e687885
        | exact resolve b3e687885 b3e96340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e687885
      have b3e687893 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e687890
           have i₂ := b3e98418
           grind)
        | exact superpose b3e98418 b3e687890
        | (have r₁ := b3e687890
           have r₂ := b3e98418
           grind)
        | exact resolve b3e687890 b3e98418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e687890
      have b3e687894 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
      clear b3e687893
      have b3e687911 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e11 (k y y)
           have i₂ := b3e687894
           grind)
        | exact superpose b3e687894 b3e11
        | exact resolve b3e11 b3e687894
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e687894
      have b3e687920 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e687911
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e687911
        | exact resolve b3e687911 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e687911
      have b3e687947 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e42 y y
           have i₂ := b3e687920
           grind)
        | exact superpose b3e687920 b3e42
        | exact resolve b3e42 b3e687920
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e42 b3e687920
      have b3e687960 : x = (M.op y y) ∨ x = y := by grind
      clear b3e687947
      have b3e733484 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e18764 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e18764
      have b3e733485 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b3e733484 X0 X1
           have j1 := b3e2574 X1 X0
           grind)
        | (have r₁ := b3e733484 (k X1 X1) X0
           have r₂ := b3e2574 X0 X1
           grind)
        | (have r₁ := b3e733484 X0 (σ (k X1 X1))
           have r₂ := b3e2574 (σ X0) X1
           grind)
        | (have r₁ := b3e733484 X1 X0
           have r₂ := b3e2574 X0 X1
           grind)
        | exact resolve b3e733484 b3e2574
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2574 b3e733484
      have b3e733502 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e20 X1 (τ X1)
           have i₂ := b3e733485 (τ X1) X0
           grind)
        | (have i₁ := b3e20 X0 X1
           have i₂ := b3e733485 X0 (σ (k (τ X0) X1))
           grind)
        | exact superpose b3e733485 b3e20
        | (have j1 := b3e733485 (τ X1) X0
           grind)
        | exact resolve b3e20 b3e733485
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e733503 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k X1 X1)
           have i₂ := b3e733485 X1 X0
           grind)
        | (have i₁ := b3e11 X0
           have i₂ := b3e733485 X0 (σ X0)
           grind)
        | exact superpose b3e733485 b3e11
        | (have j1 := b3e733485 X1 X0
           grind)
        | exact resolve b3e11 b3e733485
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e733485
      have b3e733513 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e733502 X0 X1
           have i₂ := b3e12 X1
           grind)
        | exact superpose b3e12 b3e733502
        | (have j0 := b3e733502 X0 X1
           grind)
        | exact resolve b3e733502 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e733502
      have b3e733519 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e733513 X0 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e733513
        | (have j0 := b3e733513 X0 X1
           grind)
        | exact resolve b3e733513 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e733513
      have b3e733629 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e21 X0 X1
           have i₂ := b3e733519 (τ X0) X1
           grind)
        | exact superpose b3e733519 b3e21
        | (have j1 := b3e733519 (τ X0) X1
           grind)
        | exact resolve b3e21 b3e733519
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21 b3e733519
      have b3e737567 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e733503 (σ X0) X1
           grind)
        | exact superpose b3e733503 b3e15
        | (have j1 := b3e733503 (σ X0) X1
           grind)
        | exact resolve b3e15 b3e733503
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e733503
      have b3e737571 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e737567 X0 X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e737567
        | (have j0 := b3e737567 X0 X1
           grind)
        | exact resolve b3e737567 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e737567
      have b3e737918 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e737571 x y
           grind)
        | exact superpose b3e737571 b3e16
        | (have j1 := b3e737571 x y
           grind)
        | exact resolve b3e16 b3e737571
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e737571
      have b3e738004 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e737918
           have i₂ := b3e96340
           grind)
        | exact superpose b3e96340 b3e737918
        | exact resolve b3e737918 b3e96340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e737918
      have b3e738030 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e738004
           have i₂ := b3e98418
           grind)
        | exact superpose b3e98418 b3e738004
        | (have r₁ := b3e738004
           have r₂ := b3e98418
           grind)
        | exact resolve b3e738004 b3e98418
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e98418
      have b3e738031 : x = (k y y) ∨ x = (M.op y y) := by grind
      clear b3e738030
      have b3e738130 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
        first
        | (have i₁ := b3e14 y y
           have i₂ := b3e738031
           grind)
        | exact superpose b3e738031 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e738031
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e738031
      have b3e738167 : y = (M.op y y) ∨ x = (M.op y y) := by grind
      clear b3e738130
      have b3e739196 : x ≠ y ∨ x = (M.op y y) := by grind
      clear b3e738167
      have b3e739211 : x = (M.op y y) := by
        first
        | (have r₁ := b3e739196
           have r₂ := b3e687960
           grind)
        | exact resolve b3e739196 b3e687960
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e687960 b3e739196
      have b3e739351 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e882 X0 y X1 X2
           have i₂ := b3e739211
           grind)
        | exact superpose b3e739211 b3e882
        | exact resolve b3e882 b3e739211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e882
      have b3e739529 : ∀ X0 : G, (M.op X0 x) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e10 X0 y y
           have i₂ := b3e739211
           grind)
        | exact superpose b3e739211 b3e10
        | exact resolve b3e10 b3e739211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e739804 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e1207 X0 X1 X2 y y
           have i₂ := b3e739211
           grind)
        | exact superpose b3e739211 b3e1207
        | exact resolve b3e1207 b3e739211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1207
      have b3e743373 : ∀ X0 X3 : G, (M.op X0 x) = (M.op X0 (σ (k X3 X3))) ∨ (k X3 X3) = X3 := by
        intro X0 X3
        first
        | (have i₁ := b3e96097 X3 X0 x x
           have i₂ := b3e739351 X0 x x
           grind)
        | exact superpose b3e739351 b3e96097
        | (have j0 := b3e96097 X3 x x X3
           grind)
        | exact resolve b3e96097 b3e739351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96097
      have b3e743374 : ∀ X0 X3 X4 : G, (M.op X0 x) = (M.op (σ (k X3 X4)) X0) ∨ (k X3 X4) = X3 := by
        intro X0 X3 X4
        first
        | (have i₁ := b3e96270 X3 X4 x x X0
           have i₂ := b3e739351 X0 x x
           grind)
        | exact superpose b3e739351 b3e96270
        | (have j0 := b3e96270 X3 X4 x X3 X4
           grind)
        | exact resolve b3e96270 b3e739351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96270
      have b3e743503 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 X1) x) ∨ (M.op X2 X0) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e312683 X0 X2 x X1
           have i₂ := b3e739351 (M.op X0 X1) X0 x
           grind)
        | exact superpose b3e739351 b3e312683
        | (have j0 := b3e312683 X0 X2 X2 x
           grind)
        | exact resolve b3e312683 b3e739351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e312683 b3e739351
      have b3e744607 : ∀ X0 X2 : G, (M.op x x) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X0 X2) := by
        intro X0 X2
        first
        | (have i₁ := b3e743503 X0 x X2
           have i₂ := b3e739804 X0 x x
           grind)
        | exact superpose b3e739804 b3e743503
        | (have j0 := b3e743503 X0 x X2
           grind)
        | exact resolve b3e743503 b3e739804
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e739804 b3e743503
      have b3e824454 : ∀ X0 X1 : G, x = (k x (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        grind
      clear b3e744607
      have b3e824674 : ∀ X0 : G, x = (k x x) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e824454 y X0
           have i₂ := b3e739211
           grind)
        | exact superpose b3e739211 b3e824454
        | (have j0 := b3e824454 y X0
           grind)
        | exact resolve b3e824454 b3e739211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e824454
      have b3e824699 : ∀ X0 : G, x ≠ x ∨ x = (τ (M.op (σ x) (σ x))) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e335120 x
           have i₂ := b3e824674 X0
           grind)
        | exact superpose b3e824674 b3e335120
        | (have j0 := b3e335120 x
           have j1 := b3e824674 X0
           grind)
        | (have r₁ := b3e335120 x
           have r₂ := b3e824674 X0
           grind)
        | exact resolve b3e335120 b3e824674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e335120 b3e824674
      have b3e824744 : ∀ X0 : G, x = (τ (M.op (σ x) (σ x))) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e824699 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e824699
      have b3e845171 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e12 (M.op (σ x) (σ x))
           have i₂ := b3e824744 X0
           grind)
        | exact superpose b3e824744 b3e12
        | (have j1 := b3e824744 X0
           grind)
        | exact resolve b3e12 b3e824744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e824744
      have b3e845268 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e845171 X0
           grind)
        | exact superpose b3e845171 b3e18
        | (have j1 := b3e845171 X0
           grind)
        | exact resolve b3e18 b3e845171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e845171
      have b3e848966 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e733629 (σ X0) X1
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e733629
        | exact resolve b3e733629 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e733629
      have b3e848974 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e848966 X0 X1
           have i₂ := b3e15 X1 X0
           grind)
        | exact superpose b3e15 b3e848966
        | (have j0 := b3e848966 X0 X1
           grind)
        | exact resolve b3e848966 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e848966
      have b3e848979 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
        first
        | (have i₁ := b3e848974 x y
           have i₂ := b3e96340
           grind)
        | exact superpose b3e96340 b3e848974
        | (have j0 := b3e848974 x y
           grind)
        | exact resolve b3e848974 b3e96340
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e96340 b3e848974
      have b3e849027 : x = (k y y) := by
        first
        | (have r₁ := b3e848979
           have r₂ := b3e738004
           grind)
        | exact resolve b3e848979 b3e738004
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e738004 b3e848979
      have b3e849166 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b3e743373 X0 y
           have i₂ := b3e849027
           grind)
        | exact superpose b3e849027 b3e743373
        | exact resolve b3e743373 b3e849027
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e743373
      have b3e849219 : ∀ X0 : G, (M.op X0 x) = (M.op (σ x) X0) ∨ x = y := by
        intro X0
        first
        | (have i₁ := b3e743374 X0 y y
           have i₂ := b3e849027
           grind)
        | exact superpose b3e849027 b3e743374
        | exact resolve b3e743374 b3e849027
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e743374 b3e849027
      have b3e849824 : (σ (k x y)) = (M.op (σ y) x) ∨ x = y := by
        first
        | (have i₁ := b3e202
           have i₂ := b3e849166 (σ y)
           grind)
        | exact superpose b3e849166 b3e202
        | exact resolve b3e202 b3e849166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e849166
      have b3e849946 : (σ (k x y)) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b3e849824
           have i₂ := b3e739529 (σ y)
           grind)
        | exact superpose b3e739529 b3e849824
        | exact resolve b3e849824 b3e739529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e849824
      have b3e852904 : (σ (M.op x y)) ≠ (M.op (σ y) x) ∨ x = y := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e849219 (σ y)
           grind)
        | exact superpose b3e849219 b3e16
        | exact resolve b3e16 b3e849219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e849219
      have b3e853337 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b3e852904
           have i₂ := b3e739529 (σ y)
           grind)
        | exact superpose b3e739529 b3e852904
        | exact resolve b3e852904 b3e739529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e852904
      have b3e856565 : (σ (M.op y x)) = (M.op x (σ y)) ∨ x = y ∨ x = y := by
        first
        | (have i₁ := b3e849946
           have i₂ := b3e211472
           grind)
        | exact superpose b3e211472 b3e849946
        | exact resolve b3e849946 b3e211472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e211472 b3e849946
      have b3e856645 : (σ (M.op y x)) = (M.op x (σ y)) ∨ x = y := by grind
      clear b3e856565
      have b3e856664 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
        first
        | (have i₁ := b3e856645
           have i₂ := b3e739529 y
           grind)
        | exact superpose b3e739529 b3e856645
        | exact resolve b3e856645 b3e739529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e739529 b3e856645
      have b3e856683 : x = y := by
        first
        | (have r₁ := b3e856664
           have r₂ := b3e853337
           grind)
        | exact resolve b3e856664 b3e853337
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e853337 b3e856664
      have b3e856691 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e856683
           grind)
        | exact superpose b3e856683 b3e16
        | exact resolve b3e16 b3e856683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e856693 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
        first
        | (have i₁ := b3e202
           have i₂ := b3e856683
           grind)
        | exact superpose b3e856683 b3e202
        | exact resolve b3e202 b3e856683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e202
      have b3e856867 : x = (M.op x x) := by
        first
        | (have i₁ := b3e739211
           have i₂ := b3e856683
           grind)
        | exact superpose b3e856683 b3e739211
        | exact resolve b3e739211 b3e856683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e739211
      have b3e856976 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b3e845268 X0
           have i₂ := b3e856683
           grind)
        | exact superpose b3e856683 b3e845268
        | exact resolve b3e845268 b3e856683
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e845268 b3e856683
      have b3e856998 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b3e856976 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e856976
      have b3e857155 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b3e856693
           have i₂ := b3e856998 x
           grind)
        | exact superpose b3e856998 b3e856693
        | exact resolve b3e856693 b3e856998
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e856693 b3e856998
      have b3e857156 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e856691
           have i₂ := b3e856867
           grind)
        | exact superpose b3e856867 b3e856691
        | exact resolve b3e856691 b3e856867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e856691
      have b3e857238 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e857155
           have i₂ := b3e856867
           grind)
        | exact superpose b3e856867 b3e857155
        | exact resolve b3e857155 b3e856867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e856867 b3e857155
      have b3e857288 : False := by grind
      exact b3e857288

/-- `Equation4490`: `x ◇ (y ◇ y) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4490 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4490 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4490.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y x) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 (M.op X1 X1) X3
           have i₂ := b0e10 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X1 X2 X3
           have i₂ := b0e10 X1 X2 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 (M.op X2 X2) X3 X1
           have i₂ := b0e10 X1 X2 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X2 (M.op x X0)
           have i₂ := b0e10 X0 X1 x
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 (σ x) X0 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 x X0 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e10 X2 (M.op X3 X3) X1
           have i₂ := b0e10 (M.op X1 X2) X3 X0
           grind)
        | exact superpose b0e10 b0e10
        | exact resolve b0e10 b0e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
        intro X1 X2 X3
        first
        | (have i₁ := b0e30 x X1 X2 X3
           have i₂ := b0e34 x X1 X1
           grind)
        | exact superpose b0e34 b0e30
        | exact resolve b0e30 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e34
      have b0e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 x X0 X1
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 (M.op X0 X0) X1 x
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e10
        | exact resolve b0e10 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e98 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 X0 (σ x) X1 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e31
        | exact resolve b0e31 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e99 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e31 X1 (M.op X0 X0) X2 x
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e31
        | exact resolve b0e31 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e325 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e43 (M.op X2 X2) x
           have i₂ := b0e33 X0 X1 x X2
           grind)
        | exact superpose b0e33 b0e43
        | exact resolve b0e43 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e326 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) (σ x)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e98 (σ x) (M.op X2 X2)
           have i₂ := b0e33 X0 X1 (σ x) X2
           grind)
        | exact superpose b0e33 b0e98
        | exact resolve b0e98 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e364 : ∀ X2 : G, (M.op (σ y) X2) = (M.op (σ y) (M.op X2 X2)) := by
        intro X2
        first
        | (have i₁ := b0e326 x x X2
           have i₂ := b0e98 (M.op x x) X2
           grind)
        | exact superpose b0e98 b0e326
        | exact resolve b0e326 b0e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e326
      have b0e365 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
        intro X2
        first
        | (have i₁ := b0e325 x x X2
           have i₂ := b0e43 X2 (M.op x x)
           grind)
        | exact superpose b0e43 b0e325
        | exact resolve b0e325 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e325
      have b0e447 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (M.op (σ y) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 (σ x) X1 X0
           have i₂ := b0e35 (σ x)
           grind)
        | exact superpose b0e35 b0e40
        | exact resolve b0e40 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e460 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 (M.op X1 X1) x
           have i₂ := b0e40 X1 X0 x
           grind)
        | exact superpose b0e40 b0e10
        | exact resolve b0e10 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e469 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e33 X2 X3 (M.op X0 X0) X1
           have i₂ := b0e40 X0 X0 X0
           grind)
        | exact superpose b0e40 b0e33
        | exact resolve b0e33 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e475 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
        intro X0
        first
        | (have i₁ := b0e365 (M.op X0 X0)
           have i₂ := b0e40 X0 X0 X0
           grind)
        | exact superpose b0e40 b0e365
        | exact resolve b0e365 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e491 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e31 X1 (M.op X2 (M.op X2 X2)) X3 X4
           have i₂ := b0e40 X2 X1 X0
           grind)
        | exact superpose b0e40 b0e31
        | exact resolve b0e31 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e507 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e491 x x X2 X3 X4
           have i₂ := b0e99 X2 (M.op x x) X3
           grind)
        | exact superpose b0e99 b0e491
        | exact resolve b0e491 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e491
      have b0e515 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
        intro X0
        first
        | (have i₁ := b0e475 X0
           have i₂ := b0e365 X0
           grind)
        | (have i₁ := b0e475 X0
           have i₂ := b0e365 (M.op X0 X0)
           grind)
        | exact superpose b0e365 b0e475
        | exact resolve b0e475 b0e365
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e365 b0e475
      have b0e520 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e469 X0 X1 x x
           have i₂ := b0e99 X0 (M.op x x) X1
           grind)
        | exact superpose b0e99 b0e469
        | exact resolve b0e469 b0e99
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99 b0e469
      have b0e524 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e460 X0 X1
           have i₂ := b0e40 X1 X1 X1
           grind)
        | exact superpose b0e40 b0e460
        | exact resolve b0e460 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460
      have b0e529 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e447 X0 X1
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e447
        | exact resolve b0e447 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e447
      have b0e549 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e520 X0 X1
           have i₂ := b0e507 X0 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e520 y X1
           have i₂ := b0e507 (M.op y (M.op y y)) (M.op X1 X1) x
           grind)
        | exact superpose b0e507 b0e520
        | exact resolve b0e520 b0e507
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e507 b0e520
      have b0e925 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e37 X2 (M.op x X0) (M.op X1 X1) X4
           have i₂ := b0e40 X1 X0 x
           grind)
        | exact superpose b0e40 b0e37
        | exact resolve b0e37 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1041 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 (M.op (M.op X2 X2) (M.op X2 X2))
           have i₂ := b0e37 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
           grind)
        | exact superpose b0e37 b0e36
        | exact resolve b0e36 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e37
      have b0e1094 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1041 X0 X1 X1
           have i₂ := b0e40 X1 X1 X1
           grind)
        | exact superpose b0e40 b0e1041
        | exact resolve b0e1041 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e1041
      have b0e1176 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e925 X0 X1 X2 X4
           have i₂ := b0e44 X1 (M.op X4 X4)
           grind)
        | exact superpose b0e44 b0e925
        | exact resolve b0e925 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e925
      have b0e1203 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1094 X0 X1 X2
           have i₂ := b0e524 X1 X2
           grind)
        | exact superpose b0e524 b0e1094
        | exact resolve b0e1094 b0e524
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e524 b0e1094
      have b0e1256 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) X4) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e1176 X0 X1 X2 X4
           have i₂ := b0e549 X1 X4
           grind)
        | exact superpose b0e549 b0e1176
        | exact resolve b0e1176 b0e549
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e549 b0e1176
      have b0e1268 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1203 X0 X1 X2
           have i₂ := b0e515 X2
           grind)
        | exact superpose b0e515 b0e1203
        | exact resolve b0e1203 b0e515
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e515 b0e1203
      have b0e1308 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
        intro X2
        first
        | (have i₁ := b0e1268 x x X2
           have i₂ := b0e1256 x X2 x X2
           grind)
        | exact superpose b0e1256 b0e1268
        | exact resolve b0e1268 b0e1256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1256 b0e1268
      have b0e1441 : (M.op y x) = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b0e1308 x
           have i₂ := b0e43 x y
           grind)
        | exact superpose b0e43 b0e1308
        | exact resolve b0e1308 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e1308
      have b0e1468 : y = (M.op x y) := by
        first
        | (have i₁ := b0e1441
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e1441
        | exact resolve b0e1441 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1441
      have b0e4693 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b0e98 x (M.op (σ x) (σ x))
           have i₂ := b0e529 x (σ x)
           grind)
        | exact superpose b0e529 b0e98
        | exact resolve b0e98 b0e529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98 b0e529
      have b0e4820 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b0e4693
           have i₂ := b0e364 (σ x)
           grind)
        | (have i₁ := b0e4693
           have i₂ := b0e364 (M.op (σ x) (σ x))
           grind)
        | exact superpose b0e364 b0e4693
        | exact resolve b0e4693 b0e364
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e364 b0e4693
      have b0e4915 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e4820
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e4820
        | exact resolve b0e4820 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4820
      have b0e5026 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e4915
           grind)
        | exact superpose b0e4915 b0e16
        | exact resolve b0e16 b0e4915
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4915
      have b0e5046 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e5026
           have i₂ := b0e1468
           grind)
        | exact superpose b0e1468 b0e5026
        | exact resolve b0e5026 b0e1468
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1468 b0e5026
      have b0e5047 : False := by grind
      exact b0e5047
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
        intro X0 X1 X2
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
      have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op X1 X1) X3
           have i₂ := b1e10 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X1 X2 X3
           have i₂ := b1e10 X1 X2 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
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
      have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X2 X2) X3 X1
           have i₂ := b1e10 X1 X2 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X1 X2 (M.op x X0)
           have i₂ := b1e10 X0 X1 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X2 (M.op X3 X3) X1
           have i₂ := b1e10 (M.op X1 X2) X3 X0
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
        intro X1 X2 X3
        first
        | (have i₁ := b1e27 x X1 X2 X3
           have i₂ := b1e32 x X1 X1
           grind)
        | exact superpose b1e32 b1e27
        | exact resolve b1e27 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27
      have b1e39 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 x X0 X1
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e10
        | exact resolve b1e10 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e40 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op y X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 (M.op X0 X0) X1 x
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
      have b1e93 : ∀ X0 X1 X2 : G, (M.op (M.op y X0) X2) = (M.op (M.op X1 (M.op X0 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e28 X1 (M.op X0 X0) X2 x
           have i₂ := b1e30 X0
           grind)
        | exact superpose b1e30 b1e28
        | exact resolve b1e28 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e261 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) x) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e39 (M.op X2 X2) x
           have i₂ := b1e31 X0 X1 x X2
           grind)
        | exact superpose b1e31 b1e39
        | exact resolve b1e39 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e274 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X4 X0) X1) := by
        intro X0 X1 X4
        first
        | (have i₁ := b1e28 (M.op x x) X0 X1 X4
           have i₂ := b1e31 x x X0 X1
           grind)
        | exact superpose b1e31 b1e28
        | exact resolve b1e28 b1e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e294 : ∀ X2 : G, (M.op y (M.op X2 X2)) = (M.op y X2) := by
        intro X2
        first
        | (have i₁ := b1e261 x x X2
           have i₂ := b1e39 X2 (M.op x x)
           grind)
        | exact superpose b1e39 b1e261
        | exact resolve b1e261 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e261
      have b1e311 : ∀ X0 X1 : G, (M.op y (M.op X1 X1)) = (M.op y (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e294 (M.op X1 X1)
           have i₂ := b1e10 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b1e10 b1e294
        | exact resolve b1e294 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e329 : ∀ X1 : G, (M.op y (M.op X1 X1)) = (M.op y (M.op X1 (M.op X1 X1))) := by
        intro X1
        first
        | (have i₁ := b1e311 x X1
           have i₂ := b1e32 x X1 X1
           grind)
        | exact superpose b1e32 b1e311
        | exact resolve b1e311 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32 b1e311
      have b1e330 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op X1 (M.op X1 X1))) := by
        intro X1
        first
        | (have i₁ := b1e329 X1
           have i₂ := b1e294 X1
           grind)
        | (have i₁ := b1e329 X1
           have i₂ := b1e294 (M.op X1 X1)
           grind)
        | exact superpose b1e294 b1e329
        | exact resolve b1e329 b1e294
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e329
      have b1e377 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 (M.op X1 X1) x
           have i₂ := b1e36 X1 X0 x
           grind)
        | exact superpose b1e36 b1e10
        | exact resolve b1e10 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e386 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e31 X2 X3 (M.op X0 X0) X1
           have i₂ := b1e36 X0 X0 X0
           grind)
        | exact superpose b1e36 b1e31
        | exact resolve b1e31 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31
      have b1e390 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
        intro X0
        first
        | (have i₁ := b1e294 (M.op X0 X0)
           have i₂ := b1e36 X0 X0 X0
           grind)
        | exact superpose b1e36 b1e294
        | exact resolve b1e294 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e405 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X3) = (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e28 X1 (M.op X2 (M.op X2 X2)) X3 X4
           have i₂ := b1e36 X2 X1 X0
           grind)
        | exact superpose b1e36 b1e28
        | exact resolve b1e28 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e420 : ∀ X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 (M.op X2 X2))) X3) = (M.op (M.op y X2) X3) := by
        intro X2 X3 X4
        first
        | (have i₁ := b1e405 x x X2 X3 X4
           have i₂ := b1e93 X2 (M.op x x) X3
           grind)
        | exact superpose b1e93 b1e405
        | exact resolve b1e405 b1e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e405
      have b1e428 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 (M.op X0 (M.op X0 X0)))) := by
        intro X0
        first
        | (have i₁ := b1e390 X0
           have i₂ := b1e294 X0
           grind)
        | (have i₁ := b1e390 X0
           have i₂ := b1e294 (M.op X0 X0)
           grind)
        | exact superpose b1e294 b1e390
        | exact resolve b1e390 b1e294
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e294 b1e390
      have b1e431 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e386 X0 X1 x x
           have i₂ := b1e93 X0 (M.op x x) X1
           grind)
        | exact superpose b1e93 b1e386
        | exact resolve b1e386 b1e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e93 b1e386
      have b1e436 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1)))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e377 X0 X1
           have i₂ := b1e36 X1 X1 X1
           grind)
        | exact superpose b1e36 b1e377
        | exact resolve b1e377 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e377
      have b1e457 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y X0) (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e431 X0 X1
           have i₂ := b1e420 X0 (M.op X1 X1) X0
           grind)
        | (have i₁ := b1e431 y X1
           have i₂ := b1e420 (M.op y (M.op y y)) (M.op X1 X1) x
           grind)
        | exact superpose b1e420 b1e431
        | exact resolve b1e431 b1e420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e420 b1e431
      have b1e810 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X4 X4) (M.op X4 X4))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e33 X2 (M.op x X0) (M.op X1 X1) X4
           have i₂ := b1e36 X1 X0 x
           grind)
        | exact superpose b1e36 b1e33
        | exact resolve b1e33 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e912 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X2 X2) (M.op X2 X2))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X2) (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e30 (M.op (M.op X2 X2) (M.op X2 X2))
           have i₂ := b1e33 X0 X1 (M.op (M.op X2 X2) (M.op X2 X2)) X2
           grind)
        | exact superpose b1e33 b1e30
        | exact resolve b1e30 b1e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33
      have b1e969 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 (M.op X2 X2))))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e912 X0 X1 X1
           have i₂ := b1e36 X1 X1 X1
           grind)
        | exact superpose b1e36 b1e912
        | exact resolve b1e912 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36 b1e912
      have b1e1040 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) (M.op X4 X4)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e810 X0 X1 X2 X4
           have i₂ := b1e40 X1 (M.op X4 X4)
           grind)
        | exact superpose b1e40 b1e810
        | exact resolve b1e810 b1e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40 b1e810
      have b1e1069 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 (M.op X2 (M.op X2 X2)))) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e969 X0 X1 X2
           have i₂ := b1e436 X1 X2
           grind)
        | exact superpose b1e436 b1e969
        | exact resolve b1e969 b1e436
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e436 b1e969
      have b1e1113 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y X1) X4) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X1)))) X4) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e1040 X0 X1 X2 X4
           have i₂ := b1e457 X1 X4
           grind)
        | exact superpose b1e457 b1e1040
        | exact resolve b1e1040 b1e457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e457 b1e1040
      have b1e1128 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op x (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X2 X2)))) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e1069 X0 X1 X2
           have i₂ := b1e428 X2
           grind)
        | exact superpose b1e428 b1e1069
        | exact resolve b1e1069 b1e428
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e428 b1e1069
      have b1e1166 : ∀ X2 : G, (M.op y X2) = (M.op x (M.op (M.op y X2) X2)) := by
        intro X2
        first
        | (have i₁ := b1e1128 x x X2
           have i₂ := b1e1113 x X2 x X2
           grind)
        | exact superpose b1e1113 b1e1128
        | exact resolve b1e1128 b1e1113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1113 b1e1128
      have b1e1253 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op X2 X2)) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) X2 (σ X0)
           have i₂ := b1e45 X0 X1
           grind)
        | exact superpose b1e45 b1e10
        | (have j1 := b1e45 X0 X1
           grind)
        | exact resolve b1e10 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1272 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b1e45 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e1293 : (M.op y x) = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b1e1166 x
           have i₂ := b1e39 x y
           grind)
        | exact superpose b1e39 b1e1166
        | exact resolve b1e1166 b1e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39 b1e1166
      have b1e1321 : y = (M.op x y) := by
        first
        | (have i₁ := b1e1293
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e1293
        | exact resolve b1e1293 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1293
      have b1e4590 : (M.op y x) = (M.op y (M.op y x)) := by
        first
        | (have i₁ := b1e330 x
           have i₂ := b1e30 x
           grind)
        | exact superpose b1e30 b1e330
        | exact resolve b1e330 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30 b1e330
      have b1e4628 : y = (M.op y y) := by
        first
        | (have i₁ := b1e4590
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e4590
        | exact resolve b1e4590 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4590
      have b1e4746 : y ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b1e13 y y
           have i₂ := b1e4628
           grind)
        | exact superpose b1e4628 b1e13
        | (have j0 := b1e13 y y
           grind)
        | (have r₁ := b1e13 y y
           have r₂ := b1e4628
           grind)
        | exact resolve b1e13 b1e4628
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4628
      have b1e4760 : y = (k y y) := by grind
      clear b1e4746
      have b1e16057 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e1272 y
           have i₂ := b1e4760
           grind)
        | exact superpose b1e4760 b1e1272
        | (have j0 := b1e1272 y
           grind)
        | exact resolve b1e1272 b1e4760
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1272 b1e4760
      have b1e16060 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b1e16057
      have b1e16118 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b1e274 (σ y) x (σ y)
           have i₂ := b1e16060
           grind)
        | exact superpose b1e16060 b1e274
        | exact resolve b1e274 b1e16060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e274
      have b1e159380 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        intro X0
        first
        | (have i₁ := b1e1253 x y X0
           have i₂ := b1e20
           grind)
        | exact superpose b1e20 b1e1253
        | (have j0 := b1e1253 x y x
           grind)
        | exact resolve b1e1253 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e1253
      have b1e160089 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b1e159380 X0
           grind)
        | (have r₁ := b1e159380 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e159380 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e159380
      have b1e160298 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b1e160089 X0
           have i₂ := b1e16118 X0
           grind)
        | exact superpose b1e16118 b1e160089
        | exact resolve b1e160089 b1e16118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16118 b1e160089
      have b1e160732 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e160298 (σ y)
           grind)
        | exact superpose b1e160298 b1e16
        | exact resolve b1e16 b1e160298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e160298
      have b1e161215 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b1e160732
           have i₂ := b1e16060
           grind)
        | exact superpose b1e16060 b1e160732
        | exact resolve b1e160732 b1e16060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16060 b1e160732
      have b1e161374 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e161215
           have i₂ := b1e1321
           grind)
        | exact superpose b1e1321 b1e161215
        | exact resolve b1e161215 b1e1321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1321 b1e161215
      have b1e161375 : False := by grind
      exact b1e161375
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X0) X1) := by
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
      have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X1 X1) X3
           have i₂ := b2e10 (M.op X1 X1) X1 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X1 X2 X3
           have i₂ := b2e10 X1 X2 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e33 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
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
      have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 (M.op X2 X2) X3 X1
           have i₂ := b2e10 X1 X2 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X2 (M.op x X0)
           have i₂ := b2e10 X0 X1 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op (M.op X3 X3) (M.op X3 X3))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X2 (M.op X3 X3) X1
           have i₂ := b2e10 (M.op X1 X2) X3 X0
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e39 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X1 X1)) = (M.op X2 (M.op X1 (M.op X1 X1))) := by
        intro X1 X2 X3
        first
        | (have i₁ := b2e30 x X1 X2 X3
           have i₂ := b2e35 x X1 X1
           grind)
        | exact superpose b2e35 b2e30
        | exact resolve b2e30 b2e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e30 b2e35
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
      have b2e81 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e31 X0 (σ x) X1 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e82 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
        intro X0 X1
        first
        | (have i₁ := b2e31 X0 y X1 x
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e31
        | exact resolve b2e31 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31 b2e51
      have b2e360 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (M.op (σ y) (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b2e39 (σ x) X1 X0
           have i₂ := b2e33 (σ x)
           grind)
        | exact superpose b2e33 b2e39
        | exact resolve b2e39 b2e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e33 b2e39
      have b2e426 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ x))) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e360 X0 X1
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e360
        | exact resolve b2e360 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e360
      have b2e1113 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e34 x x (σ x) X0
           have i₂ := b2e81 (M.op x x) X0
           grind)
        | exact superpose b2e81 b2e34
        | exact resolve b2e34 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e1149 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b2e1113 X0
           have i₂ := b2e81 (σ x) (M.op X0 X0)
           grind)
        | exact superpose b2e81 b2e1113
        | exact resolve b2e1113 b2e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1113
      have b2e2763 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (σ x)) = (M.op X2 (M.op (σ x) (σ y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e36 X0 X1 X2 (σ x)
           have i₂ := b2e426 (σ x) (σ x)
           grind)
        | exact superpose b2e426 b2e36
        | exact resolve b2e36 b2e426
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36
      have b2e2769 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b2e81 x (M.op (σ x) (σ x))
           have i₂ := b2e426 x (σ x)
           grind)
        | exact superpose b2e426 b2e81
        | exact resolve b2e81 b2e426
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e81
      have b2e2787 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X2 (M.op X1 X0)) (σ x)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X1 X0) (σ x) X2
           have i₂ := b2e426 X1 X0
           grind)
        | exact superpose b2e426 b2e10
        | exact resolve b2e10 b2e426
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2808 : (M.op (σ y) (M.op (σ x) (σ x))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e1149 (M.op (σ x) (σ x))
           have i₂ := b2e426 (σ x) (σ x)
           grind)
        | exact superpose b2e426 b2e1149
        | exact resolve b2e1149 b2e426
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e426
      have b2e2837 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e2808
           have i₂ := b2e1149 (σ x)
           grind)
        | exact superpose b2e1149 b2e2808
        | exact resolve b2e2808 b2e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2808
      have b2e2869 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e2769
           have i₂ := b2e1149 (σ x)
           grind)
        | exact superpose b2e1149 b2e2769
        | exact resolve b2e2769 b2e1149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1149 b2e2769
      have b2e2874 : ∀ X2 : G, (M.op X2 (σ y)) = (M.op X2 (M.op (σ x) (σ y))) := by
        intro X2
        first
        | (have i₁ := b2e2763 x x X2
           have i₂ := b2e2787 X2 x x
           grind)
        | exact superpose b2e2787 b2e2763
        | exact resolve b2e2763 b2e2787
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2763 b2e2787
      have b2e2917 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
        first
        | (have i₁ := b2e2837
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2837
        | exact resolve b2e2837 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2837
      have b2e2937 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b2e2869
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e2869
        | exact resolve b2e2869 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2869
      have b2e2968 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e2917
           have i₂ := b2e2874 (σ y)
           grind)
        | exact superpose b2e2874 b2e2917
        | exact resolve b2e2917 b2e2874
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2874 b2e2917
      have b2e3032 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b2e16
           have i₂ := b2e2937
           grind)
        | exact superpose b2e2937 b2e16
        | exact resolve b2e16 b2e2937
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2937
      have b2e3050 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e3032
           have i₂ := b2e50
           grind)
        | exact superpose b2e50 b2e3032
        | exact resolve b2e3032 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3032
      have b2e3499 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ y) (σ y)
           have i₂ := b2e2968
           grind)
        | exact superpose b2e2968 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | (have r₁ := b2e13 (σ y) (σ y)
           have r₂ := b2e2968
           grind)
        | exact resolve b2e13 b2e2968
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2968
      have b2e3513 : (σ y) = (k (σ y) (σ y)) := by grind
      clear b2e3499
      have b2e3516 : (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b2e3513
           have i₂ := b2e15 y y
           grind)
        | exact superpose b2e15 b2e3513
        | exact resolve b2e3513 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3513
      have b2e3545 : (k y y) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k y y)
           have i₂ := b2e3516
           grind)
        | exact superpose b2e3516 b2e11
        | exact resolve b2e11 b2e3516
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3516
      have b2e3566 : y = (k y y) := by
        first
        | (have i₁ := b2e3545
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e3545
        | exact resolve b2e3545 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3545
      have b2e3612 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e14 y y
           have i₂ := b2e3566
           grind)
        | exact superpose b2e3566 b2e14
        | (have j0 := b2e14 y y
           grind)
        | exact resolve b2e14 b2e3566
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3566
      have b2e3613 : y = (M.op y y) := by grind
      clear b2e3612
      have b2e3663 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b2e82 y X0
           have i₂ := b2e3613
           grind)
        | exact superpose b2e3613 b2e82
        | exact resolve b2e82 b2e3613
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82
      have b2e4262 : (σ x) = (σ (M.op y y)) := by
        first
        | (have i₁ := b2e50
           have i₂ := b2e3663 y
           grind)
        | exact superpose b2e3663 b2e50
        | exact resolve b2e50 b2e3663
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50 b2e3663
      have b2e4335 : (σ x) = (σ y) := by
        first
        | (have i₁ := b2e4262
           have i₂ := b2e3613
           grind)
        | exact superpose b2e3613 b2e4262
        | exact resolve b2e4262 b2e3613
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e3613 b2e4262
      have b2e4352 : False := by grind
      exact b2e4352
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
      have b3e35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b3e1218 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e35 x y
           grind)
        | exact superpose b3e35 b3e16
        | (have j1 := b3e35 x y
           grind)
        | exact resolve b3e16 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e1262 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e1218
           have r₂ := b3e18
           grind)
        | exact resolve b3e1218 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1218
      have b3e1271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b3e1262
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e1262
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e1262 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1262
      have b3e1272 : y = (M.op y x) := by grind
      clear b3e1271
      have b3e1273 : False := by grind
      exact b3e1273

/-- `Equation4519`: `x ◇ (y ◇ z) = (x ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4519 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4519 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4519.models_iff G M).mp hM
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
    · have b1e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X1) := by
        intro X0 X1 X2 X3
        grind
      have b1e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b1e24 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X0) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e10 X3 X0 (M.op X2 x) X5
           have i₂ := b1e10 X0 X2 x X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X5) (M.op X0 X4)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e10 X3 (M.op X0 X4) X1 X5
           have i₂ := b1e10 X0 X1 X2 X4
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X1 X2 x
           have i₂ := b1e10 X0 X1 X3 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 X3) ∨ (k X0 (M.op X2 X3)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X0 (M.op X2 X3)
           have i₂ := b1e10 X0 X2 X3 X1
           grind)
        | exact superpose b1e10 b1e13
        | (have j0 := b1e13 X0 (M.op X2 X3)
           grind)
        | (have r₁ := b1e13 X0 (M.op (M.op X0 X3) (M.op X0 X3))
           have r₂ := b1e10 X0 (M.op X0 X3) (M.op X0 X3) X3
           grind)
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
      have b1e153 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 X0 x X1 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e31
        | exact resolve b1e31 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e252 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X5) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e10 X0 (M.op X2 X3) x X5
           have i₂ := b1e24 X2 X3 x X0 X1
           grind)
        | exact superpose b1e24 b1e10
        | exact resolve b1e10 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e968 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X2) x) := by
        intro X0 X2
        first
        | (have i₁ := b1e10 X0 x x X2
           have i₂ := b1e153 X0 x
           grind)
        | exact superpose b1e153 b1e10
        | exact resolve b1e10 b1e153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e153
      have b1e1434 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 := by
        intro X0 X1
        first
        | (have j0 := b1e33 X0 X1 (M.op X0 X1) (M.op X0 X1)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e33
      have b1e1738 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e51 y x
           grind)
        | exact superpose b1e51 b1e18
        | (have j1 := b1e51 y x
           grind)
        | (have r₁ := b1e18
           have r₂ := b1e51 y x
           grind)
        | exact resolve b1e18 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e1767 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b1e1738
      have b1e1769 : (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b1e1767
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e1767
        | exact resolve b1e1767 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21 b1e1767
      have b1e1781 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (σ y) (M.op X2 X3))) = (M.op (M.op X0 X1) (σ x)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e25 (σ y) X2 X3 X0 (σ x) X1
           have i₂ := b1e1769
           grind)
        | exact superpose b1e1769 b1e25
        | exact resolve b1e25 b1e1769
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e1790 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e31 X0 (σ y) X1 (σ x)
           have i₂ := b1e1769
           grind)
        | exact superpose b1e1769 b1e31
        | exact resolve b1e31 b1e1769
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31
      have b1e1797 : (M.op (σ y) y) = (M.op (σ x) x) := by
        first
        | (have i₁ := b1e968 (σ y) (σ x)
           have i₂ := b1e1769
           grind)
        | exact superpose b1e1769 b1e968
        | exact resolve b1e968 b1e1769
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1799 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 X1) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1781 X0 X1 x x
           have i₂ := b1e1790 X0 (M.op x x)
           grind)
        | exact superpose b1e1790 b1e1781
        | exact resolve b1e1781 b1e1790
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1781 b1e1790
      have b1e3755 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b1e1434 X0 x
           have i₂ := b1e252 X0 X1 X0 x x
           grind)
        | exact superpose b1e252 b1e1434
        | exact resolve b1e1434 b1e252
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e252 b1e1434
      have b1e3929 : (σ x) = (k (σ x) (M.op (M.op (σ y) y) (σ x))) := by
        first
        | (have i₁ := b1e3755 (σ x) x
           have i₂ := b1e1797
           grind)
        | exact superpose b1e1797 b1e3755
        | exact resolve b1e3755 b1e1797
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1797 b1e3755
      have b1e3989 : (σ x) = (k (σ x) (M.op (σ y) (σ x))) := by
        first
        | (have i₁ := b1e3929
           have i₂ := b1e1799 (σ y) y
           grind)
        | exact superpose b1e1799 b1e3929
        | exact resolve b1e3929 b1e1799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1799 b1e3929
      have b1e4000 : (σ x) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b1e3989
           have i₂ := b1e1769
           grind)
        | exact superpose b1e1769 b1e3989
        | exact resolve b1e3989 b1e1769
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e3989
      have b1e4008 : (σ x) = (σ (k x x)) := by
        first
        | (have i₁ := b1e4000
           have i₂ := b1e15 x x
           grind)
        | exact superpose b1e15 b1e4000
        | exact resolve b1e4000 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4000
      have b1e4431 : (k x x) = (τ (σ x)) := by
        first
        | (have i₁ := b1e11 (k x x)
           have i₂ := b1e4008
           grind)
        | exact superpose b1e4008 b1e11
        | exact resolve b1e11 b1e4008
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4008
      have b1e4444 : x = (k x x) := by
        first
        | (have i₁ := b1e4431
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e4431
        | exact resolve b1e4431 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4431
      have b1e4531 : x = (M.op x x) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b1e14 x x
           have i₂ := b1e4444
           grind)
        | exact superpose b1e4444 b1e14
        | (have j0 := b1e14 x x
           grind)
        | exact resolve b1e14 b1e4444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4444
      have b1e4532 : x = (M.op x x) := by grind
      clear b1e4531
      have b1e4588 : (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b1e968 x x
           have i₂ := b1e4532
           grind)
        | exact superpose b1e4532 b1e968
        | exact resolve b1e968 b1e4532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e968
      have b1e4594 : x = (M.op x y) := by
        first
        | (have i₁ := b1e4588
           have i₂ := b1e4532
           grind)
        | exact superpose b1e4532 b1e4588
        | exact resolve b1e4588 b1e4532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4532 b1e4588
      have b1e4602 : x = y := by
        first
        | (have i₁ := b1e4594
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e4594
        | exact resolve b1e4594 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4594
      have b1e4635 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e4602
           grind)
        | exact superpose b1e4602 b1e18
        | exact resolve b1e18 b1e4602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4646 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e1769
           have i₂ := b1e4602
           grind)
        | exact superpose b1e4602 b1e1769
        | exact resolve b1e1769 b1e4602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1769 b1e4602
      have b1e4655 : False := by grind
      exact b1e4655
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X1) := by
        intro X0 X1 X2 X3
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b2e17 : y ≠ (M.op x y) := by grind
      have b2e18 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
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
      have b2e31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ x) (σ y) X1
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : x = (M.op y x) ∨ y = (M.op x y) := by
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
      have b2e54 : x = (M.op y x) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e56 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 y X0 X1 x
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e10
        | exact resolve b2e10 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54
      have b2e73 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e31 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e147 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e31 (σ y) (σ x)
           have i₂ := b2e73
           grind)
        | exact superpose b2e73 b2e31
        | exact resolve b2e31 b2e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e152 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b2e147
           have i₂ := b2e73
           grind)
        | exact superpose b2e73 b2e147
        | exact resolve b2e147 b2e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e73 b2e147
      have b2e189 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ y) (σ y)
           have i₂ := b2e152
           grind)
        | exact superpose b2e152 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | (have r₁ := b2e13 (σ y) (σ y)
           have r₂ := b2e152
           grind)
        | exact resolve b2e13 b2e152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e152
      have b2e194 : (σ y) = (k (σ y) (σ y)) := by grind
      clear b2e189
      have b2e195 : (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b2e194
           have i₂ := b2e15 y y
           grind)
        | exact superpose b2e15 b2e194
        | exact resolve b2e194 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e194
      have b2e280 : (k y y) = (τ (σ y)) := by
        first
        | (have i₁ := b2e11 (k y y)
           have i₂ := b2e195
           grind)
        | exact superpose b2e195 b2e11
        | exact resolve b2e11 b2e195
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e195
      have b2e281 : y = (k y y) := by
        first
        | (have i₁ := b2e280
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e280
        | exact resolve b2e280 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e280
      have b2e422 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b2e14 y y
           have i₂ := b2e281
           grind)
        | exact superpose b2e281 b2e14
        | (have j0 := b2e14 y y
           grind)
        | exact resolve b2e14 b2e281
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e281
      have b2e423 : y = (M.op y y) := by grind
      clear b2e422
      have b2e913 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e56 y y
           have i₂ := b2e423
           grind)
        | exact superpose b2e423 b2e56
        | exact resolve b2e56 b2e423
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56
      have b2e965 : y = (M.op x y) := by
        first
        | (have i₁ := b2e913
           have i₂ := b2e423
           grind)
        | exact superpose b2e423 b2e913
        | exact resolve b2e913 b2e423
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e423 b2e913
      have b2e984 : False := by grind
      exact b2e984
    · have b3e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X1) := by
        intro X0 X1 X2 X3
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
      have b3e21 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X5) X0) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b3e10 X3 X0 (M.op X2 x) X5
           have i₂ := b3e10 X0 X2 x X1
           grind)
        | exact superpose b3e10 b3e10
        | exact resolve b3e10 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X2 X3) ∨ (k X0 (M.op X2 X3)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b3e13 X0 (M.op X2 X3)
           have i₂ := b3e10 X0 X2 X3 X1
           grind)
        | exact superpose b3e10 b3e13
        | (have j0 := b3e13 X0 (M.op X2 X3)
           grind)
        | (have r₁ := b3e13 X0 (M.op (M.op X0 X3) (M.op X0 X3))
           have r₂ := b3e10 X0 (M.op X0 X3) (M.op X0 X3) X3
           grind)
        | exact resolve b3e13 b3e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
      have b3e192 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X5) (M.op X2 X3)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b3e10 X0 (M.op X2 X3) x X5
           have i₂ := b3e21 X2 X3 x X0 X1
           grind)
        | exact superpose b3e21 b3e10
        | exact resolve b3e10 b3e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21
      have b3e1607 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X0 := by
        intro X0 X1
        first
        | (have j0 := b3e29 X0 X1 (M.op X0 X1) (M.op X0 X1)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e29
      have b3e1633 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e1607 X0 x
           have i₂ := b3e192 X0 X1 X0 x x
           grind)
        | exact superpose b3e192 b3e1607
        | exact resolve b3e1607 b3e192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e192 b3e1607
      have b3e1778 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e36 x y
           grind)
        | exact superpose b3e36 b3e16
        | (have j1 := b3e36 x y
           grind)
        | exact resolve b3e16 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1779 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e36 x y
           grind)
        | exact superpose b3e36 b3e18
        | (have j1 := b3e36 x y
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e36 y x
           grind)
        | exact resolve b3e18 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1815 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e36 y x
           grind)
        | exact superpose b3e36 b3e18
        | (have j1 := b3e36 y x
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e36 y x
           grind)
        | exact resolve b3e18 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e1850 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e36 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e1852 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
      clear b3e1815
      have b3e1855 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e1779
           have i₂ := b3e1852
           grind)
        | exact superpose b3e1852 b3e1779
        | exact resolve b3e1779 b3e1852
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1779
      have b3e1856 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e1778
           have i₂ := b3e1852
           grind)
        | exact superpose b3e1852 b3e1778
        | exact resolve b3e1778 b3e1852
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1778
      have b3e1917 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (σ (k x y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 X0 (σ y) (σ x) X1
           have i₂ := b3e1852
           grind)
        | exact superpose b3e1852 b3e10
        | exact resolve b3e10 b3e1852
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1852
      have b3e12196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e1856
           have i₂ := b3e14 y x
           grind)
        | exact superpose b3e14 b3e1856
        | (have j1 := b3e14 y x
           grind)
        | exact resolve b3e1856 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1856
      have b3e12197 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by grind
      clear b3e12196
      have b3e12205 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e11 (k x y)
           have i₂ := b3e12197
           grind)
        | exact superpose b3e12197 b3e11
        | exact resolve b3e11 b3e12197
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12197
      have b3e12236 : x = (k x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e12205
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e12205
        | exact resolve b3e12205 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12205
      have b3e12308 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
        first
        | (have i₁ := b3e14 x y
           have i₂ := b3e12236
           grind)
        | exact superpose b3e12236 b3e14
        | (have j0 := b3e14 y x
           grind)
        | exact resolve b3e14 b3e12236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12236
      have b3e12309 : x = (M.op y x) ∨ y = (M.op x y) := by grind
      clear b3e12308
      have b3e12311 : x = (M.op y x) := by
        first
        | (have r₁ := b3e12309
           have r₂ := b3e17
           grind)
        | exact resolve b3e12309 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12309
      have b3e13140 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 y X0 X1 x
           have i₂ := b3e12311
           grind)
        | exact superpose b3e12311 b3e10
        | exact resolve b3e10 b3e12311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e13141 : x ≠ x ∨ y = (k y x) := by
        first
        | (have i₁ := b3e13 y x
           have i₂ := b3e12311
           grind)
        | exact superpose b3e12311 b3e13
        | (have j0 := b3e13 y x
           grind)
        | (have r₁ := b3e13 y x
           have r₂ := b3e12311
           grind)
        | exact resolve b3e13 b3e12311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e13207 : y = (k y x) := by grind
      clear b3e13141
      have b3e14078 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
        first
        | (have i₁ := b3e1855
           have i₂ := b3e13207
           grind)
        | exact superpose b3e13207 b3e1855
        | exact resolve b3e1855 b3e13207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1855 b3e13207
      have b3e14080 : (σ x) = (σ (k x y)) := by grind
      clear b3e14078
      have b3e20017 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b3e13140 y x
           have i₂ := b3e12311
           grind)
        | exact superpose b3e12311 b3e13140
        | exact resolve b3e13140 b3e12311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20018 : ∀ X0 : G, (M.op x y) = (M.op y (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b3e13140 y (M.op X0 x)
           have i₂ := b3e13140 X0 x
           grind)
        | exact superpose b3e13140 b3e13140
        | exact resolve b3e13140 b3e13140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20271 : (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b3e20018 x
           have i₂ := b3e13140 x x
           grind)
        | exact superpose b3e13140 b3e20018
        | exact resolve b3e20018 b3e13140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e13140 b3e20018
      have b3e20272 : x = (M.op x y) := by
        first
        | (have i₁ := b3e20017
           have i₂ := b3e12311
           grind)
        | exact superpose b3e12311 b3e20017
        | exact resolve b3e20017 b3e12311
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e12311 b3e20017
      have b3e21468 : x = (k x (M.op x x)) := by
        first
        | (have i₁ := b3e1633 x y
           have i₂ := b3e20272
           grind)
        | exact superpose b3e20272 b3e1633
        | exact resolve b3e1633 b3e20272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1633
      have b3e21485 : x = (k x (M.op x y)) := by
        first
        | (have i₁ := b3e21468
           have i₂ := b3e20271
           grind)
        | exact superpose b3e20271 b3e21468
        | exact resolve b3e21468 b3e20271
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20271 b3e21468
      have b3e21489 : x = (k x x) := by
        first
        | (have i₁ := b3e21485
           have i₂ := b3e20272
           grind)
        | exact superpose b3e20272 b3e21485
        | exact resolve b3e21485 b3e20272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e21485
      have b3e24986 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e1850 x
           have i₂ := b3e21489
           grind)
        | exact superpose b3e21489 b3e1850
        | (have j0 := b3e1850 x
           grind)
        | exact resolve b3e1850 b3e21489
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1850 b3e21489
      have b3e24989 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e24986
      have b3e27668 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x y))) := by
        first
        | (have i₁ := b3e1917 (σ x) (σ x)
           have i₂ := b3e24989
           grind)
        | exact superpose b3e24989 b3e1917
        | exact resolve b3e1917 b3e24989
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1917
      have b3e27673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e27668
           have i₂ := b3e14080
           grind)
        | exact superpose b3e14080 b3e27668
        | exact resolve b3e27668 b3e14080
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e14080 b3e27668
      have b3e27682 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e27673
           have i₂ := b3e24989
           grind)
        | exact superpose b3e24989 b3e27673
        | exact resolve b3e27673 b3e24989
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e24989 b3e27673
      have b3e28479 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e27682
           grind)
        | exact superpose b3e27682 b3e16
        | exact resolve b3e16 b3e27682
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27682
      have b3e28597 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b3e28479
           have i₂ := b3e20272
           grind)
        | exact superpose b3e20272 b3e28479
        | exact resolve b3e28479 b3e20272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20272 b3e28479
      have b3e28598 : False := by grind
      exact b3e28598

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4535 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4535 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
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
    · have b1e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
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
      have b1e24 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x y X1
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b1e10 X3 X2 (M.op X0 x) X5
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X3) X0 X3
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e27 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b1e10 X2 X0 x X4
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 (M.op X1 x) X1 X2 x
           have i₂ := b1e10 (M.op X1 X2) X1 X2 x
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 x X1 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e10
        | exact resolve b1e10 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e10 X3 X2 X4 (M.op X0 x)
           have i₂ := b1e10 X2 X0 x X1
           grind)
        | (have i₁ := b1e10 X0 (M.op X1 X3) X2 X0
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 X0 X1 X2 x
           have i₂ := b1e10 X0 X1 X3 x
           grind)
        | (have i₁ := b1e10 (M.op X1 X2) X1 X2 X3
           have i₂ := b1e10 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 X3) ∨ (k X2 (M.op X0 X3)) = X2 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X2 (M.op X0 X3)
           have i₂ := b1e10 X2 X0 X3 X1
           grind)
        | (have i₁ := b1e13 (M.op X1 X3) X0
           have i₂ := b1e10 X0 X1 X2 X3
           grind)
        | exact superpose b1e10 b1e13
        | (have j0 := b1e13 X2 (M.op X0 X3)
           grind)
        | exact resolve b1e13 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36 : ∀ X0 : G, (M.op X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e24 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e24
        | exact resolve b1e24 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b1e61 : y = (M.op y x) := by
        first
        | (have i₁ := b1e17
           have i₂ := b1e36 x
           grind)
        | exact superpose b1e36 b1e17
        | exact resolve b1e17 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e85 : ∀ X0 X1 : G, (M.op y X0) = (M.op X0 (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y X1 x
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e10
        | exact resolve b1e10 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e86 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b1e10 X0 y x X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e10
        | exact resolve b1e10 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
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
      have b1e92 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b1e94 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e23 X1 X0
           have i₂ := b1e14 X0 (τ X1)
           grind)
        | exact superpose b1e14 b1e23
        | (have j1 := b1e14 X0 (τ X1)
           grind)
        | exact resolve b1e23 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b1e148 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e27 X0 X1 X2 y
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e27 y X1 X2 X0
           have i₂ := b1e36 X0
           grind)
        | exact superpose b1e36 b1e27
        | exact resolve b1e27 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e178 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X2 X5) (M.op X0 X4)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b1e27 X0 X4 (M.op X2 X3) X1
           grind)
        | (have i₁ := b1e10 (M.op X0 X4) X2 X3 X5
           have i₂ := b1e27 X0 X1 (M.op X2 X3) X4
           grind)
        | exact superpose b1e27 b1e10
        | exact resolve b1e10 b1e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e191 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e148 X0 X1 X2
           have i₂ := b1e86 X2 X0
           grind)
        | exact superpose b1e86 b1e148
        | exact resolve b1e148 b1e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e86 b1e148
      have b1e271 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op y X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e32 X1 X0 X2 y
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e32 X0 y X2 X0
           have i₂ := b1e36 X0
           grind)
        | exact superpose b1e36 b1e32
        | exact resolve b1e32 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e312 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (k X0 (M.op X1 X3)) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e13 X0 (M.op X1 X3)
           have i₂ := b1e32 X0 X1 X3 X2
           grind)
        | (have i₁ := b1e13 X0 (M.op X1 X3)
           have i₂ := b1e32 X0 X1 X2 X3
           grind)
        | exact superpose b1e32 b1e13
        | (have j0 := b1e13 X0 (M.op X1 X3)
           grind)
        | (have r₁ := b1e13 X0 (M.op X0 (M.op X0 X3))
           have r₂ := b1e32 X0 X0 (M.op X0 X3) X3
           grind)
        | (have r₁ := b1e13 X0 (M.op X0 (M.op X0 X2))
           have r₂ := b1e32 X0 X0 X2 (M.op X0 X2)
           grind)
        | exact resolve b1e13 b1e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e336 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op y X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e271 X0 X1 X2
           have i₂ := b1e85 X1 X0
           grind)
        | exact superpose b1e85 b1e271
        | exact resolve b1e271 b1e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e85 b1e271
      have b1e501 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e32 X2 (M.op X3 X4) X0 X5
           have i₂ := b1e25 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b1e32 (M.op X2 X5) X1 X2 X3
           have i₂ := b1e25 X0 X1 X2 (M.op X1 X2) X5
           grind)
        | exact superpose b1e25 b1e32
        | exact resolve b1e32 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e32
      have b1e505 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X0) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e13 X2 (M.op (M.op X3 X4) X0)
           have i₂ := b1e25 X3 X4 X0 X2 X1
           grind)
        | (have i₁ := b1e13 (M.op X2 x) X3
           have i₂ := b1e25 X0 X1 X2 X3 x
           grind)
        | exact superpose b1e25 b1e13
        | (have j0 := b1e13 X2 (M.op (M.op X3 X4) X0)
           grind)
        | (have r₁ := b1e13 X3 (M.op (M.op X3 x) X3)
           have r₂ := b1e25 X3 x X3 X3 x
           grind)
        | exact resolve b1e13 b1e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e530 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 y) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b1e505 X0 X1 X2 X3 X4
           have i₂ := b1e191 X3 X4 X0
           grind)
        | exact superpose b1e191 b1e505
        | (have j0 := b1e505 X0 X1 X2 X3 X4
           grind)
        | (have r₁ := b1e505 y X1 (M.op X3 X4) X3 X4
           have r₂ := b1e191 y X1 (M.op X3 X4)
           grind)
        | exact resolve b1e505 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e505
      have b1e532 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e501 X0 X1 X2 x x x
           have i₂ := b1e336 (M.op x x) X2 x
           grind)
        | exact superpose b1e336 b1e501
        | exact resolve b1e501 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e501
      have b1e586 : ∀ X0 X2 X3 X4 : G, (M.op X0 y) ≠ (M.op X2 y) ∨ (k X2 (M.op (M.op X3 X4) X0)) = X2 := by
        intro X0 X2 X3 X4
        first
        | (have i₁ := b1e530 X0 x X2 X3 X4
           have i₂ := b1e191 X0 x X2
           grind)
        | exact superpose b1e191 b1e530
        | (have j0 := b1e530 X0 x X2 X3 X4
           grind)
        | (have r₁ := b1e530 X2 x X2 X3 X4
           have r₂ := b1e191 X2 x X2
           grind)
        | exact resolve b1e530 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e530
      have b1e620 : ∀ X0 X2 : G, (M.op X0 y) ≠ (M.op X2 y) ∨ (k X2 (M.op X0 y)) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b1e586 X0 X2 x x
           have i₂ := b1e191 x x X0
           grind)
        | exact superpose b1e191 b1e586
        | (have j0 := b1e586 X0 X2 x x
           grind)
        | (have r₁ := b1e586 (M.op X0 x) y x x
           have r₂ := b1e191 X0 x y
           grind)
        | (have r₁ := b1e586 y (M.op X0 x) x x
           have r₂ := b1e191 X0 x y
           grind)
        | exact resolve b1e586 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e586
      have b1e831 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X3 X4) X5) X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b1e27 (M.op X3 X4) X5 X0 X1
           have i₂ := b1e30 X3 X4 X1 X0 X2
           grind)
        | (have i₁ := b1e27 X0 X1 (M.op X2 X4) X4
           have i₂ := b1e30 X0 X1 X2 (M.op X0 X4) X4
           grind)
        | exact superpose b1e30 b1e27
        | exact resolve b1e27 b1e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27 b1e30
      have b1e865 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e831 X0 X1 X2 x x x
           have i₂ := b1e191 (M.op x x) x X0
           grind)
        | exact superpose b1e191 b1e831
        | exact resolve b1e831 b1e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e191 b1e831
      have b1e4066 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) ≠ (M.op (σ (k X0 X1)) X2) ∨ (k X2 (M.op (σ X0) X3)) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e34 (σ X0) (σ X1) X2 X3
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e34
        | (have j0 := b1e34 (σ X0) X1 X2 X3
           have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e34 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34
      have b1e4071 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e532 (σ X0) (σ X1) X2
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e532
        | (have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e532 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4072 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e865 X2 (σ X0) (σ X1)
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e865
        | (have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e865 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e865
      have b1e4073 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b1e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4284 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b1e92 X1 (τ X0)
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e92
        | exact resolve b1e92 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4288 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e92 X0 X1
           have i₂ := b1e14 X0 (σ X1)
           grind)
        | exact superpose b1e14 b1e92
        | (have j1 := b1e14 X0 (σ X1)
           grind)
        | exact resolve b1e92 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e4493 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e99 X0 X1
           have i₂ := b1e14 (σ X0) X1
           grind)
        | exact superpose b1e14 b1e99
        | (have j1 := b1e14 (σ X0) X1
           grind)
        | exact resolve b1e99 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e7978 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 := by
        intro X0
        first
        | (have j0 := b1e620 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e620
      have b1e7997 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e7978 X0
           have i₂ := b1e36 X0
           grind)
        | (have i₁ := b1e7978 y
           have i₂ := b1e36 y
           grind)
        | exact superpose b1e36 b1e7978
        | exact resolve b1e7978 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8013 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e7978 (M.op X0 X1)
           have i₂ := b1e532 X0 X1 y
           grind)
        | exact superpose b1e532 b1e7978
        | exact resolve b1e7978 b1e532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8022 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) := by
        intro X0
        first
        | (have i₁ := b1e99 X0 (M.op (σ X0) y)
           have i₂ := b1e7978 (σ X0)
           grind)
        | exact superpose b1e7978 b1e99
        | exact resolve b1e99 b1e7978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8023 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) y))) := by
        intro X0
        first
        | (have i₁ := b1e22 X0 (M.op (τ X0) y)
           have i₂ := b1e7978 (τ X0)
           grind)
        | exact superpose b1e7978 b1e22
        | exact resolve b1e22 b1e7978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e8024 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op y (τ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e8023 X0
           have i₂ := b1e36 (τ X0)
           grind)
        | exact superpose b1e36 b1e8023
        | exact resolve b1e8023 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8023
      have b1e8025 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op y (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b1e8022 X0
           have i₂ := b1e36 (σ X0)
           grind)
        | exact superpose b1e36 b1e8022
        | exact resolve b1e8022 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8022
      have b1e8039 : ∀ X0 : G, (k X0 (σ (M.op y (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e8024 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e8024
        | exact resolve b1e8024 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8024
      have b1e8040 : ∀ X0 : G, (k X0 (τ (M.op y (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e8025 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e8025
        | exact resolve b1e8025 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8025
      have b1e8311 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op y (σ (σ X0)))))) := by
        intro X0
        first
        | (have i₁ := b1e99 X0 (τ (M.op y (σ (σ X0))))
           have i₂ := b1e8040 (σ X0)
           grind)
        | exact superpose b1e8040 b1e99
        | exact resolve b1e99 b1e8040
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e99
      have b1e8316 : ∀ X0 : G, (k X0 (τ (τ (M.op y (σ (σ X0)))))) = X0 := by
        intro X0
        first
        | (have i₁ := b1e8311 X0
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e8311
        | exact resolve b1e8311 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8311
      have b1e13950 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 y)) ∨ (σ (M.op X0 y)) = (M.op (σ X0) (σ (M.op X0 y))) := by
        intro X0
        first
        | (have i₁ := b1e4073 X0 (M.op X0 y)
           have i₂ := b1e7978 X0
           grind)
        | exact superpose b1e7978 b1e4073
        | (have j0 := b1e4073 X0 (M.op X0 y)
           grind)
        | exact resolve b1e4073 b1e7978
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7978
      have b1e13960 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e4073 (τ X0) (τ X1)
           have i₂ := b1e4284 X1 X0
           grind)
        | exact superpose b1e4284 b1e4073
        | (have j0 := b1e4073 (τ X0) (τ X1)
           grind)
        | exact resolve b1e4073 b1e4284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e13963 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b1e4073 x y
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e4073
        | (have j0 := b1e4073 x y
           grind)
        | exact resolve b1e4073 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e13968 : (σ x) ≠ (σ y) := by
        first
        | (have r₁ := b1e13963
           have r₂ := b1e18
           grind)
        | exact resolve b1e13963 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13963
      have b1e13969 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e13960 X0 X1
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e13960
        | (have j0 := b1e13960 X0 X1
           grind)
        | exact resolve b1e13960 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13960
      have b1e13973 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b1e13969 X0 X1
           have i₂ := b1e12 X1
           grind)
        | exact superpose b1e12 b1e13969
        | (have j0 := b1e13969 X0 X1
           grind)
        | exact resolve b1e13969 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13969
      have b1e13976 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e13973 X0 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13973
        | (have j0 := b1e13973 X0 X1
           grind)
        | exact resolve b1e13973 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13973
      have b1e13977 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b1e13976 X0 X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e13976
        | (have j0 := b1e13976 X0 X1
           grind)
        | exact resolve b1e13976 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13976
      have b1e14002 : ∀ X0 : G, (σ (M.op y (τ X0))) = (k X0 (σ y)) ∨ y = (M.op y (τ X0)) := by
        intro X0
        first
        | (have i₁ := b1e89 X0 y
           have i₂ := b1e36 (τ X0)
           grind)
        | exact superpose b1e36 b1e89
        | exact resolve b1e89 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e89
      have b1e14103 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e13977 (τ X0) (τ X1)
           have i₂ := b1e4284 X1 X0
           grind)
        | exact superpose b1e4284 b1e13977
        | (have j0 := b1e13977 (τ X0) (τ X1)
           grind)
        | exact resolve b1e13977 b1e4284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e14464 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) ≠ (M.op X2 (σ (k X0 X1))) ∨ (k X2 (M.op (σ X0) X3)) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e312 X2 (σ X0) (σ X1) X3
           have i₂ := b1e51 X0 X1
           grind)
        | exact superpose b1e51 b1e312
        | (have j0 := b1e312 X2 (σ X0) X2 X3
           have j1 := b1e51 X0 X1
           grind)
        | exact resolve b1e312 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51 b1e312
      have b1e14847 : ∀ X0 X1 X2 : G, (σ (M.op y (τ X0))) = (k (σ (M.op X1 X2)) X0) ∨ (τ X0) = (M.op y (τ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e94 (M.op X0 X1) X1
           have i₂ := b1e532 X0 X1 (τ X1)
           grind)
        | exact superpose b1e532 b1e94
        | (have j0 := b1e94 y X0
           grind)
        | exact resolve b1e94 b1e532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e94
      have b1e15860 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X1) ∨ (k X1 (M.op (σ x) X0)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e4066 x y X1 X0
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e4066
        | (have j0 := b1e4066 x y X1 X0
           grind)
        | exact resolve b1e4066 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4066
      have b1e15911 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X1) ∨ (k X1 (M.op (σ x) X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e15860 X0 X1
           grind)
        | (have r₁ := b1e15860 X0 X1
           have r₂ := b1e18
           grind)
        | exact resolve b1e15860 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15860
      have b1e16815 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k X0 (τ y)) ∨ y = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e4493 X0 y
           have i₂ := b1e36 (σ X0)
           grind)
        | exact superpose b1e36 b1e4493
        | exact resolve b1e4493 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e16922 : ∀ X0 : G, (σ (M.op y X0)) = (k (σ X0) (σ y)) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e14002 (σ X0)
           have i₂ := b1e11 X0
           grind)
        | exact superpose b1e11 b1e14002
        | exact resolve b1e14002 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14002
      have b1e16970 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k X0 y)) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e16922 X0
           have i₂ := b1e15 X0 y
           grind)
        | exact superpose b1e15 b1e16922
        | (have j0 := b1e16922 X0
           grind)
        | exact resolve b1e16922 b1e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16922
      have b1e17057 : ∀ X0 X1 X2 : G, (τ (M.op y (σ X0))) = (k (τ (M.op X1 X2)) X0) ∨ (σ X0) = (M.op y (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e4288 (M.op X0 X1) X1
           have i₂ := b1e532 X0 X1 (σ X1)
           grind)
        | exact superpose b1e532 b1e4288
        | (have j0 := b1e4288 y X0
           grind)
        | exact resolve b1e4288 b1e532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e532
      have b1e17201 : ∀ X0 : G, (k X0 y) = (τ (σ (M.op y X0))) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e11 (k X0 y)
           have i₂ := b1e16970 X0
           grind)
        | exact superpose b1e16970 b1e11
        | (have j1 := b1e16970 X0
           grind)
        | exact resolve b1e11 b1e16970
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16970
      have b1e17244 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e17201 X0
           have i₂ := b1e11 (M.op y X0)
           grind)
        | exact superpose b1e11 b1e17201
        | (have j0 := b1e17201 X0
           grind)
        | exact resolve b1e17201 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17201
      have b1e17289 : ∀ X0 : G, (k X0 (M.op (σ x) X0)) = X0 := by
        intro X0
        first
        | (have j0 := b1e15911 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e15911
      have b1e17395 : y = (k y (M.op y (σ x))) := by
        first
        | (have i₁ := b1e17289 y
           have i₂ := b1e36 (σ x)
           grind)
        | exact superpose b1e36 b1e17289
        | exact resolve b1e17289 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17289
      have b1e17595 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e4071 (τ X0) (τ X1) X2
           have i₂ := b1e4284 X1 X0
           grind)
        | exact superpose b1e4284 b1e4071
        | (have j0 := b1e4071 (τ X0) (τ X1) X2
           grind)
        | exact resolve b1e4071 b1e4284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e17598 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e4071 x y X0
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e4071
        | (have j0 := b1e4071 x y x
           grind)
        | exact resolve b1e4071 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4071
      have b1e17813 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b1e17598 X0
           grind)
        | (have r₁ := b1e17598 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e17598 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17598
      have b1e17814 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e17595 X0 X1 X2
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e17595
        | (have j0 := b1e17595 X0 X1 X2
           grind)
        | exact resolve b1e17595 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17595
      have b1e17862 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op y X2) = (M.op (k X0 X1) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e17814 X0 X0 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e17814
        | (have j0 := b1e17814 X0 X1 X2
           grind)
        | exact resolve b1e17814 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17814
      have b1e17892 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e17862 X0 X1 X2
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e17862
        | (have j0 := b1e17862 X0 X1 X2
           grind)
        | exact resolve b1e17862 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17862
      have b1e17926 : ∀ X0 : G, (τ (M.op y X0)) = (k x (τ X0)) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e4493 x X0
           have i₂ := b1e17813 X0
           grind)
        | exact superpose b1e17813 b1e4493
        | exact resolve b1e4493 b1e17813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4493
      have b1e17928 : (σ y) ≠ (M.op y (σ y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e17813 (σ y)
           grind)
        | exact superpose b1e17813 b1e18
        | exact resolve b1e18 b1e17813
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17813
      have b1e18204 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e4072 x y X0
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e4072
        | (have j0 := b1e4072 x y x
           grind)
        | exact resolve b1e4072 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4072
      have b1e18437 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b1e18204 X0
           grind)
        | (have r₁ := b1e18204 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e18204 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18204
      have b1e18916 : x = (k x (τ (M.op y y))) := by
        first
        | (have i₁ := b1e8040 x
           have i₂ := b1e18437 y
           grind)
        | exact superpose b1e18437 b1e8040
        | exact resolve b1e8040 b1e18437
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18437
      have b1e26504 : ∀ X0 : G, (M.op y X0) = (σ (k x (τ X0))) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e12 (M.op y X0)
           have i₂ := b1e17926 X0
           grind)
        | exact superpose b1e17926 b1e12
        | (have j1 := b1e17926 X0
           grind)
        | exact resolve b1e12 b1e17926
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17926
      have b1e26553 : ∀ X0 : G, (M.op y X0) = (k (σ x) X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b1e26504 X0
           have i₂ := b1e23 X0 x
           grind)
        | exact superpose b1e23 b1e26504
        | (have j0 := b1e26504 X0
           grind)
        | exact resolve b1e26504 b1e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23 b1e26504
      have b1e27427 : (σ x) = (M.op y (σ (M.op y (τ (σ x))))) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e8039 (σ x)
           have i₂ := b1e26553 (σ (M.op y (τ (σ x))))
           grind)
        | exact superpose b1e26553 b1e8039
        | (have j1 := b1e26553 (σ (M.op y (τ (σ x))))
           grind)
        | exact resolve b1e8039 b1e26553
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26553
      have b1e27477 : (σ x) = (M.op y (σ (M.op y x))) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e27427
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27427
        | exact resolve b1e27427 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27427
      have b1e27509 : (σ x) = (M.op y (σ y)) ∨ (σ (M.op y (τ (σ x)))) = (M.op y (σ (M.op y (τ (σ x))))) := by
        first
        | (have i₁ := b1e27477
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e27477
        | exact resolve b1e27477 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27477
      have b1e27530 : (σ (M.op y x)) = (M.op y (σ (M.op y x))) ∨ (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e27509
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27509
        | exact resolve b1e27509 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27509
      have b1e27544 : (σ y) = (M.op y (σ y)) ∨ (σ x) = (M.op y (σ y)) := by
        first
        | (have i₁ := b1e27530
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e27530
        | exact resolve b1e27530 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27530
      have b1e27556 : (σ x) = (M.op y (σ y)) := by
        first
        | (have r₁ := b1e27544
           have r₂ := b1e17928
           grind)
        | exact resolve b1e27544 b1e17928
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27544
      have b1e27734 : (τ (σ x)) = (k (τ y) y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b1e4288 y y
           have i₂ := b1e27556
           grind)
        | exact superpose b1e27556 b1e4288
        | exact resolve b1e4288 b1e27556
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4288
      have b1e27814 : (τ (σ x)) = (k (τ y) y) := by
        first
        | (have r₁ := b1e27734
           have r₂ := b1e13968
           grind)
        | exact resolve b1e27734 b1e13968
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27734
      have b1e27835 : x = (k (τ y) y) := by
        first
        | (have i₁ := b1e27814
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e27814
        | exact resolve b1e27814 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27814
      have b1e28192 : (σ x) = (k y (σ y)) := by
        first
        | (have i₁ := b1e22 y y
           have i₂ := b1e27835
           grind)
        | exact superpose b1e27835 b1e22
        | exact resolve b1e22 b1e27835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e28209 : x = (M.op y (τ y)) ∨ y = (M.op y (τ y)) := by
        first
        | (have i₁ := b1e17244 (τ y)
           have i₂ := b1e27835
           grind)
        | exact superpose b1e27835 b1e17244
        | (have j0 := b1e17244 (τ y)
           grind)
        | exact resolve b1e17244 b1e27835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17244
      have b1e30406 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X0 X3)) = (M.op (M.op X0 X1) (M.op y X2)) ∨ y = (M.op y (τ y)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e178 X0 X1 y X2 X3 (τ y)
           have i₂ := b1e28209
           grind)
        | exact superpose b1e28209 b1e178
        | exact resolve b1e178 b1e28209
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28209
      have b1e30426 : ∀ X0 X1 X3 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op X0 X3)) ∨ y = (M.op y (τ y)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e30406 X0 X1 x X3
           have i₂ := b1e336 y (M.op X0 X1) x
           grind)
        | exact superpose b1e336 b1e30406
        | exact resolve b1e30406 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30406
      have b1e30459 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y x) ∨ y = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e30426 X0 X1 x
           have i₂ := b1e336 X0 x x
           grind)
        | exact superpose b1e336 b1e30426
        | exact resolve b1e30426 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30426
      have b1e30470 : ∀ X0 X1 : G, y = (M.op y (M.op X0 X1)) ∨ y = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e30459 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e30459
        | exact resolve b1e30459 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30459
      have b1e30479 : y = (M.op y (τ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e30470 x x
           have i₂ := b1e336 x y x
           grind)
        | exact superpose b1e336 b1e30470
        | exact resolve b1e30470 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30470
      have b1e30721 : y = (k y (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e8039 y
           have i₂ := b1e30479
           grind)
        | exact superpose b1e30479 b1e8039
        | exact resolve b1e8039 b1e30479
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8039
      have b1e30734 : (τ y) = (k (τ y) y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e7997 (τ y)
           have i₂ := b1e30479
           grind)
        | exact superpose b1e30479 b1e7997
        | exact resolve b1e7997 b1e30479
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30479
      have b1e30804 : y = (M.op y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e30734
           have i₂ := b1e27835
           grind)
        | exact superpose b1e27835 b1e30734
        | exact resolve b1e30734 b1e27835
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27835 b1e30734
      have b1e30806 : y = (M.op y y) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e30721
           have i₂ := b1e28192
           grind)
        | exact superpose b1e28192 b1e30721
        | exact resolve b1e30721 b1e28192
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28192 b1e30721
      have b1e31100 : y = (k y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e8013 y y
           have i₂ := b1e30804
           grind)
        | exact superpose b1e30804 b1e8013
        | exact resolve b1e8013 b1e30804
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30804
      have b1e31720 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e4073 y y
           have i₂ := b1e31100
           grind)
        | exact superpose b1e31100 b1e4073
        | (have j0 := b1e4073 y y
           grind)
        | exact resolve b1e4073 b1e31100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4073 b1e31100
      have b1e31731 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (τ y) := by grind
      clear b1e31720
      have b1e34838 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) ≠ (M.op X3 (σ (τ (k X0 X1)))) ∨ (k X3 (M.op (σ (τ X0)) X2)) = X3 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e14464 (τ X0) (τ X1) X3 X2
           have i₂ := b1e4284 X1 X0
           grind)
        | exact superpose b1e4284 b1e14464
        | (have j0 := b1e14464 (τ X0) (τ X1) X3 X2
           grind)
        | exact resolve b1e14464 b1e4284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e4284 b1e14464
      have b1e34996 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X2) ≠ (M.op X3 (k X0 X1)) ∨ (k X3 (M.op (σ (τ X0)) X2)) = X3 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e34838 X0 X1 X2 X3
           have i₂ := b1e12 (k X0 X1)
           grind)
        | exact superpose b1e12 b1e34838
        | (have j0 := b1e34838 X0 X1 X2 X3
           grind)
        | exact resolve b1e34838 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34838
      have b1e35067 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op X3 (k X0 X1)) ∨ (k X3 (M.op (σ (τ X0)) X2)) = X3 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e34996 X0 X1 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e34996
        | (have j0 := b1e34996 X0 X1 X2 X3
           grind)
        | exact resolve b1e34996 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e34996
      have b1e35109 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 X2)) = X3 ∨ (M.op X0 X2) ≠ (M.op X3 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e35067 X0 X1 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e35067
        | (have j0 := b1e35067 X0 X1 X2 X3
           grind)
        | exact resolve b1e35067 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35067
      have b1e35138 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X3 (M.op X0 X2)) = X3 ∨ (M.op X0 X2) ≠ (M.op X3 (k X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e35109 X0 X0 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e35109
        | (have j0 := b1e35109 X0 X1 X2 X3
           grind)
        | exact resolve b1e35109 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35109
      have b1e35162 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op X3 (k X0 X1)) ∨ (k X3 (M.op X0 X2)) = X3 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e35138 X0 X1 X2 X3
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e35138
        | (have j0 := b1e35138 X0 X1 X2 X3
           grind)
        | exact resolve b1e35138 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35138
      have b1e35222 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (σ y) X2)) = (M.op (σ y) (M.op X0 X3)) ∨ x = (τ y) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e178 X0 X1 (σ y) X2 X3 (σ y)
           have i₂ := b1e31731
           grind)
        | exact superpose b1e31731 b1e178
        | exact resolve b1e178 b1e31731
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e31731
      have b1e35240 : ∀ X0 X1 X2 : G, (M.op y (σ y)) = (M.op (M.op X0 X1) (M.op (σ y) X2)) ∨ x = (τ y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e35222 X0 X1 X2 x
           have i₂ := b1e336 X0 (σ y) x
           grind)
        | exact superpose b1e336 b1e35222
        | exact resolve b1e35222 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35222
      have b1e35269 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (σ y)) ∨ x = (τ y) := by
        intro X0 X1
        first
        | (have i₁ := b1e35240 X0 X1 x
           have i₂ := b1e336 (σ y) (M.op X0 X1) x
           grind)
        | exact superpose b1e336 b1e35240
        | exact resolve b1e35240 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35240
      have b1e35282 : ∀ X0 X1 : G, (σ x) = (M.op y (M.op X0 X1)) ∨ x = (τ y) := by
        intro X0 X1
        first
        | (have i₁ := b1e35269 X0 X1
           have i₂ := b1e27556
           grind)
        | exact superpose b1e27556 b1e35269
        | exact resolve b1e35269 b1e27556
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35269
      have b1e35290 : (σ x) = (M.op y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e35282 x x
           have i₂ := b1e336 x y x
           grind)
        | exact superpose b1e336 b1e35282
        | exact resolve b1e35282 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35282
      have b1e35679 : y = (σ x) ∨ y = (σ x) ∨ x = (τ y) := by
        first
        | (have i₁ := b1e30806
           have i₂ := b1e35290
           grind)
        | exact superpose b1e35290 b1e30806
        | exact resolve b1e30806 b1e35290
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e30806 b1e35290
      have b1e35767 : x = (τ y) ∨ y = (σ x) := by grind
      clear b1e35679
      have b1e36193 : y = (σ x) ∨ y = (σ x) := by
        first
        | (have i₁ := b1e12 y
           have i₂ := b1e35767
           grind)
        | exact superpose b1e35767 b1e12
        | exact resolve b1e12 b1e35767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35767
      have b1e36269 : y = (σ x) := by grind
      clear b1e36193
      have b1e36686 : y ≠ (σ y) := by
        first
        | (have i₁ := b1e13968
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e13968
        | exact resolve b1e13968 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13968
      have b1e36706 : x = (τ y) := by
        first
        | (have i₁ := b1e11 x
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e11
        | exact resolve b1e11 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36708 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) y) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 x
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e15
        | exact resolve b1e15 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e36715 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b1e92 X0 x
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e92
        | exact resolve b1e92 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e92
      have b1e36729 : x = (k x (τ (τ (M.op y (σ y))))) := by
        first
        | (have i₁ := b1e8316 x
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e8316
        | exact resolve b1e8316 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8316
      have b1e36757 : x = (k x (τ (τ (σ x)))) := by
        first
        | (have i₁ := b1e36729
           have i₂ := b1e27556
           grind)
        | exact superpose b1e27556 b1e36729
        | exact resolve b1e36729 b1e27556
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36729
      have b1e36763 : x = (k x (τ x)) := by
        first
        | (have i₁ := b1e36757
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e36757
        | exact resolve b1e36757 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36757
      have b1e38072 : (τ x) = (M.op x (τ x)) ∨ x = (M.op x (τ x)) := by
        first
        | (have i₁ := b1e14 x (τ x)
           have i₂ := b1e36763
           grind)
        | exact superpose b1e36763 b1e14
        | (have j0 := b1e14 x (τ x)
           grind)
        | exact resolve b1e14 b1e36763
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e38087 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0
        first
        | (have i₁ := b1e17892 x (τ x) X0
           have i₂ := b1e36763
           grind)
        | exact superpose b1e36763 b1e17892
        | (have j0 := b1e17892 x (τ x) x
           grind)
        | exact resolve b1e17892 b1e36763
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17892 b1e36763
      have b1e39900 : ∀ X0 : G, y ≠ (σ (k X0 x)) ∨ y = (M.op (σ X0) y) := by
        intro X0
        first
        | (have i₁ := b1e13977 (σ X0) y
           have i₂ := b1e36708 X0
           grind)
        | exact superpose b1e36708 b1e13977
        | (have j0 := b1e13977 (σ X0) y
           grind)
        | exact resolve b1e13977 b1e36708
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13977 b1e36708
      have b1e39914 : ∀ X0 : G, y ≠ (σ (k X0 x)) ∨ y = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e39900 X0
           have i₂ := b1e36 (σ X0)
           grind)
        | exact superpose b1e36 b1e39900
        | (have j0 := b1e39900 X0
           grind)
        | exact resolve b1e39900 b1e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36 b1e39900
      have b1e40168 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X1))) x) = (τ (σ (M.op y (τ y)))) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e36715 (σ (M.op X0 X1))
           have i₂ := b1e14847 y X0 X1
           grind)
        | exact superpose b1e14847 b1e36715
        | (have j1 := b1e14847 y X1 x
           grind)
        | exact resolve b1e36715 b1e14847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14847
      have b1e40173 : (τ x) = (k (τ x) x) := by
        first
        | (have i₁ := b1e36715 x
           have i₂ := b1e21
           grind)
        | exact superpose b1e21 b1e36715
        | exact resolve b1e36715 b1e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e21
      have b1e40286 : ∀ X0 X1 : G, (M.op y (τ y)) = (k (τ (σ (M.op X0 X1))) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e40168 X0 X1
           have i₂ := b1e11 (M.op y (τ y))
           grind)
        | exact superpose b1e11 b1e40168
        | exact resolve b1e40168 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40168
      have b1e40289 : ∀ X0 X1 : G, (k (M.op X0 X1) x) = (M.op y (τ y)) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e40286 X0 X1
           have i₂ := b1e11 (M.op X0 X1)
           grind)
        | exact superpose b1e11 b1e40286
        | exact resolve b1e40286 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40286
      have b1e40290 : ∀ X0 X1 : G, (M.op y x) = (k (M.op X0 X1) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e40289 X0 X1
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e40289
        | exact resolve b1e40289 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40289
      have b1e40291 : ∀ X0 X1 : G, y = (k (M.op X0 X1) x) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e40290 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e40290
        | exact resolve b1e40290 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40290
      have b1e40292 : ∀ X0 X1 : G, x = (M.op y x) ∨ y = (k (M.op X0 X1) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e40291 X0 X1
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e40291
        | (have j0 := b1e40291 X0 X1
           grind)
        | exact resolve b1e40291 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40291
      have b1e40293 : ∀ X0 X1 : G, y = (k (M.op X0 X1) x) ∨ x = y := by
        intro X0 X1
        first
        | (have i₁ := b1e40292 X0 X1
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e40292
        | (have j0 := b1e40292 X0 X1
           grind)
        | exact resolve b1e40292 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40292
      have b1e51622 : ∀ X0 : G, y ≠ (k X0 (σ x)) ∨ y = (M.op y (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e39914 (τ X0)
           have i₂ := b1e22 X0 x
           grind)
        | exact superpose b1e22 b1e39914
        | (have j0 := b1e39914 (τ X0)
           grind)
        | exact resolve b1e39914 b1e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e39914
      have b1e51659 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op y (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b1e51622 X0
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e51622
        | (have j0 := b1e51622 X0
           grind)
        | exact resolve b1e51622 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51622
      have b1e51677 : ∀ X0 : G, y ≠ (k X0 y) ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b1e51659 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e51659
        | (have j0 := b1e51659 X0
           grind)
        | exact resolve b1e51659 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51659
      have b1e67731 : y = (k (τ x) x) ∨ x = y ∨ x = (M.op x (τ x)) := by
        first
        | (have i₁ := b1e40293 x (τ x)
           have i₂ := b1e38072
           grind)
        | exact superpose b1e38072 b1e40293
        | exact resolve b1e40293 b1e38072
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38072
      have b1e67734 : x = (M.op x (τ x)) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e67731
           have i₂ := b1e40173
           grind)
        | exact superpose b1e40173 b1e67731
        | exact resolve b1e67731 b1e40173
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40173 b1e67731
      have b1e77192 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op x X2)) = (M.op x (M.op X0 X3)) ∨ x = y ∨ y = (τ x) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e178 X0 X1 x X2 X3 (τ x)
           have i₂ := b1e67734
           grind)
        | exact superpose b1e67734 b1e178
        | exact resolve b1e178 b1e67734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e178
      have b1e77214 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e40293 x (τ x)
           have i₂ := b1e67734
           grind)
        | exact superpose b1e67734 b1e40293
        | exact resolve b1e40293 b1e67734
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e40293 b1e67734
      have b1e77219 : y = (k x x) ∨ x = y ∨ y = (τ x) := by grind
      clear b1e77214
      have b1e77229 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x X2)) = (M.op y x) ∨ x = y ∨ y = (τ x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e77192 X0 X1 X2 x
           have i₂ := b1e336 X0 x x
           grind)
        | exact superpose b1e336 b1e77192
        | exact resolve b1e77192 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e77192
      have b1e77272 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) (M.op x X2)) ∨ x = y ∨ y = (τ x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e77229 X0 X1 X2
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e77229
        | exact resolve b1e77229 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e77229
      have b1e77295 : ∀ X0 X1 : G, y = (M.op y (M.op X0 X1)) ∨ x = y ∨ y = (τ x) := by
        intro X0 X1
        first
        | (have i₁ := b1e77272 X0 X1 x
           have i₂ := b1e29 (M.op X0 X1) x
           grind)
        | exact superpose b1e29 b1e77272
        | exact resolve b1e77272 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e77272
      have b1e77305 : y = (M.op y y) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e77295 x x
           have i₂ := b1e336 x y x
           grind)
        | exact superpose b1e336 b1e77295
        | exact resolve b1e77295 b1e336
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e77295
      have b1e78302 : x = (k x (τ y)) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e18916
           have i₂ := b1e77305
           grind)
        | exact superpose b1e77305 b1e18916
        | exact resolve b1e18916 b1e77305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e18916 b1e77305
      have b1e78430 : x = (k x x) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e78302
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e78302
        | exact resolve b1e78302 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e78302
      have b1e79193 : x = y ∨ x = y ∨ y = (τ x) ∨ x = y ∨ y = (τ x) := by
        first
        | (have i₁ := b1e77219
           have i₂ := b1e78430
           grind)
        | exact superpose b1e78430 b1e77219
        | exact resolve b1e77219 b1e78430
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e77219 b1e78430
      have b1e79224 : y = (τ x) ∨ x = y := by grind
      clear b1e79193
      have b1e102972 : ∀ X0 X1 : G, (τ (τ (M.op y (σ y)))) = (k (τ (τ (M.op X0 X1))) x) ∨ (σ y) = (M.op y (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e36715 (τ (M.op X0 X1))
           have i₂ := b1e17057 y X0 X1
           grind)
        | exact superpose b1e17057 b1e36715
        | (have j1 := b1e17057 y X1 x
           grind)
        | exact resolve b1e36715 b1e17057
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17057 b1e36715
      have b1e102973 : ∀ X0 X1 : G, (τ (τ (M.op y (σ y)))) = (k (τ (τ (M.op X0 X1))) x) := by
        intro X0 X1
        first
        | (have j0 := b1e102972 X0 X1
           grind)
        | (have r₁ := b1e102972 X0 X1
           have r₂ := b1e17928
           grind)
        | exact resolve b1e102972 b1e17928
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17928 b1e102972
      have b1e102987 : ∀ X0 X1 : G, (τ (τ (σ x))) = (k (τ (τ (M.op X0 X1))) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e102973 X0 X1
           have i₂ := b1e27556
           grind)
        | exact superpose b1e27556 b1e102973
        | exact resolve b1e102973 b1e27556
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e27556 b1e102973
      have b1e102998 : ∀ X0 X1 : G, (τ x) = (k (τ (τ (M.op X0 X1))) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e102987 X0 X1
           have i₂ := b1e11 x
           grind)
        | exact superpose b1e11 b1e102987
        | exact resolve b1e102987 b1e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e102987
      have b1e103128 : ∀ X0 X1 : G, (σ (τ x)) = (k (τ (M.op X0 X1)) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b1e22 (τ (M.op X0 X1)) x
           have i₂ := b1e102998 X0 X1
           grind)
        | exact superpose b1e102998 b1e22
        | exact resolve b1e22 b1e102998
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e102998
      have b1e103194 : ∀ X0 X1 : G, (σ (τ x)) = (k (τ (M.op X0 X1)) y) := by
        intro X0 X1
        first
        | (have i₁ := b1e103128 X0 X1
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e103128
        | exact resolve b1e103128 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103128
      have b1e103225 : ∀ X0 X1 : G, x = (k (τ (M.op X0 X1)) y) := by
        intro X0 X1
        first
        | (have i₁ := b1e103194 X0 X1
           have i₂ := b1e12 x
           grind)
        | exact superpose b1e12 b1e103194
        | exact resolve b1e103194 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103194
      have b1e103472 : ∀ X0 : G, x = (k (k X0 (τ y)) y) ∨ y = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e103225 y (σ X0)
           have i₂ := b1e16815 X0
           grind)
        | exact superpose b1e16815 b1e103225
        | (have j1 := b1e16815 X0
           grind)
        | exact resolve b1e103225 b1e16815
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e16815
      have b1e103479 : ∀ X0 X1 : G, (σ x) = (k (M.op X0 X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e22 (M.op X0 X1) y
           have i₂ := b1e103225 X0 X1
           grind)
        | exact superpose b1e103225 b1e22
        | exact resolve b1e22 b1e103225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e103548 : ∀ X0 X1 : G, y = (k (M.op X0 X1) (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e103479 X0 X1
           have i₂ := b1e36269
           grind)
        | exact superpose b1e36269 b1e103479
        | exact resolve b1e103479 b1e36269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36269 b1e103479
      have b1e103552 : ∀ X0 : G, x = (k (k X0 x) y) ∨ y = (M.op y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e103472 X0
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e103472
        | (have j0 := b1e103472 X0
           grind)
        | exact resolve b1e103472 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103472
      have b1e112821 : ∀ X0 X1 : G, (k X0 (M.op X0 (k X0 X1))) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b1e35162 X0 X1 (k X0 X1) X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e35162
      have b1e118488 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op y x) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0
        first
        | (have i₁ := b1e29 x X0
           have i₂ := b1e38087 (M.op x X0)
           grind)
        | exact superpose b1e38087 b1e29
        | exact resolve b1e29 b1e38087
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e38087
      have b1e118608 : ∀ X0 : G, y = (M.op y (M.op x X0)) ∨ (τ x) = (M.op x (τ x)) := by
        intro X0
        first
        | (have i₁ := b1e118488 X0
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e118488
        | exact resolve b1e118488 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e118488
      have b1e118687 : (τ x) = (M.op x (τ x)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e118608 x
           have i₂ := b1e29 y x
           grind)
        | exact superpose b1e29 b1e118608
        | exact resolve b1e118608 b1e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29 b1e118608
      have b1e118830 : ∀ X0 : G, (M.op y X0) = (M.op X0 (τ x)) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b1e336 x X0 (τ x)
           have i₂ := b1e118687
           grind)
        | exact superpose b1e118687 b1e336
        | exact resolve b1e336 b1e118687
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e336
      have b1e119737 : (M.op y x) = (τ x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e118687
           have i₂ := b1e118830 x
           grind)
        | exact superpose b1e118830 b1e118687
        | exact resolve b1e118687 b1e118830
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e118687 b1e118830
      have b1e119780 : (M.op y x) = (τ x) ∨ y = (M.op y y) := by grind
      clear b1e119737
      have b1e119794 : y = (M.op y y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e119780
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e119780
        | exact resolve b1e119780 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119780
      have b1e120100 : y = (k y y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e8013 y y
           have i₂ := b1e119794
           grind)
        | exact superpose b1e119794 b1e8013
        | exact resolve b1e8013 b1e119794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e119794
      have b1e120241 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e14103 y y
           have i₂ := b1e120100
           grind)
        | exact superpose b1e120100 b1e14103
        | (have j0 := b1e14103 y y
           grind)
        | exact resolve b1e14103 b1e120100
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e14103 b1e120100
      have b1e120252 : (τ y) = (M.op (τ y) (τ y)) ∨ y = (τ x) := by grind
      clear b1e120241
      have b1e120266 : x = (M.op x x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e120252
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e120252
        | exact resolve b1e120252 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e120252
      have b1e120408 : x = (k (τ x) y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e103225 x x
           have i₂ := b1e120266
           grind)
        | exact superpose b1e120266 b1e103225
        | exact resolve b1e103225 b1e120266
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103225 b1e120266
      have b1e120516 : x ≠ y ∨ y = (M.op y (τ x)) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e51677 (τ x)
           have i₂ := b1e120408
           grind)
        | exact superpose b1e120408 b1e51677
        | (have j0 := b1e51677 (τ x)
           grind)
        | exact resolve b1e51677 b1e120408
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e120551 : y = (M.op y (τ x)) ∨ y = (τ x) := by
        first
        | (have r₁ := b1e120516
           have r₂ := b1e79224
           grind)
        | exact resolve b1e120516 b1e79224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e120516
      have b1e120667 : (τ x) = (k (τ x) y) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e7997 (τ x)
           have i₂ := b1e120551
           grind)
        | exact superpose b1e120551 b1e7997
        | exact resolve b1e7997 b1e120551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e120551
      have b1e123210 : x = (τ x) ∨ y = (τ x) ∨ y = (τ x) := by
        first
        | (have i₁ := b1e120408
           have i₂ := b1e120667
           grind)
        | exact superpose b1e120667 b1e120408
        | exact resolve b1e120408 b1e120667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e120408 b1e120667
      have b1e123259 : x = (τ x) ∨ y = (τ x) := by grind
      clear b1e123210
      have b1e123460 : x ≠ y ∨ y = (τ x) := by grind
      clear b1e123259
      have b1e123470 : y = (τ x) := by
        first
        | (have r₁ := b1e123460
           have r₂ := b1e79224
           grind)
        | exact resolve b1e123460 b1e79224
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e79224 b1e123460
      have b1e123570 : x = (σ y) := by
        first
        | (have i₁ := b1e12 x
           have i₂ := b1e123470
           grind)
        | exact superpose b1e123470 b1e12
        | exact resolve b1e12 b1e123470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e123571 : ∀ X0 : G, (k x (σ X0)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b1e22 x X0
           have i₂ := b1e123470
           grind)
        | exact superpose b1e123470 b1e22
        | exact resolve b1e22 b1e123470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e22 b1e123470
      have b1e123869 : x ≠ y := by
        first
        | (have i₁ := b1e36686
           have i₂ := b1e123570
           grind)
        | exact superpose b1e123570 b1e36686
        | exact resolve b1e36686 b1e123570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e123895 : ∀ X0 X1 : G, y = (k (M.op X0 X1) x) := by
        intro X0 X1
        first
        | (have i₁ := b1e103548 X0 X1
           have i₂ := b1e123570
           grind)
        | exact superpose b1e123570 b1e103548
        | exact resolve b1e103548 b1e123570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e124274 : ∀ X0 X1 : G, y = (M.op y (σ (M.op X0 X1))) ∨ x = (k y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e103552 (M.op X0 X1)
           have i₂ := b1e123895 X0 X1
           grind)
        | exact superpose b1e123895 b1e103552
        | (have j0 := b1e103552 (M.op X0 X1)
           grind)
        | exact resolve b1e103552 b1e123895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103552
      have b1e134004 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (τ y)) ∨ x = (k y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e8040 (M.op X0 X1)
           have i₂ := b1e124274 X0 X1
           grind)
        | exact superpose b1e124274 b1e8040
        | exact resolve b1e8040 b1e124274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8040 b1e124274
      have b1e134126 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) x) ∨ x = (k y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e134004 X0 X1
           have i₂ := b1e36706
           grind)
        | exact superpose b1e36706 b1e134004
        | exact resolve b1e134004 b1e36706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e36706 b1e134004
      have b1e134153 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ x = (k y y) := by
        intro X0 X1
        first
        | (have i₁ := b1e134126 X0 X1
           have i₂ := b1e123895 X0 X1
           grind)
        | exact superpose b1e123895 b1e134126
        | exact resolve b1e134126 b1e123895
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123895 b1e134126
      have b1e134563 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (k y y) := by
        intro X0
        first
        | (have i₁ := b1e7997 X0
           have i₂ := b1e134153 y X0
           grind)
        | exact superpose b1e134153 b1e7997
        | exact resolve b1e7997 b1e134153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e7997
      have b1e134578 : x = (k y y) ∨ y = (k y y) := by
        first
        | (have i₁ := b1e17395
           have i₂ := b1e134153 y (σ x)
           grind)
        | exact superpose b1e134153 b1e17395
        | exact resolve b1e17395 b1e134153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e17395 b1e134153
      have b1e135323 : y = (k y (M.op y x)) ∨ y = (M.op y y) ∨ y = (k y y) := by
        first
        | (have i₁ := b1e112821 y y
           have i₂ := b1e134578
           grind)
        | exact superpose b1e134578 b1e112821
        | (have j0 := b1e112821 y y
           grind)
        | exact resolve b1e112821 b1e134578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e112821 b1e134578
      have b1e135329 : y = (k y (M.op y x)) ∨ y = (M.op y y) := by
        first
        | (have j1 := b1e51677 y
           grind)
        | (have r₁ := b1e135323
           have r₂ := b1e51677 y
           grind)
        | exact resolve b1e135323 b1e51677
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e135323
      have b1e135373 : y = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b1e135329
           have i₂ := b1e61
           grind)
        | exact superpose b1e61 b1e135329
        | exact resolve b1e135329 b1e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e61 b1e135329
      have b1e135398 : y = (M.op y y) := by
        first
        | (have j1 := b1e51677 y
           grind)
        | (have r₁ := b1e135373
           have r₂ := b1e51677 y
           grind)
        | exact resolve b1e135373 b1e51677
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51677 b1e135373
      have b1e135474 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b1e13950 y
           have i₂ := b1e135398
           grind)
        | exact superpose b1e135398 b1e13950
        | exact resolve b1e13950 b1e135398
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e13950
      have b1e135521 : y = (k y y) := by
        first
        | (have i₁ := b1e8013 y y
           have i₂ := b1e135398
           grind)
        | exact superpose b1e135398 b1e8013
        | exact resolve b1e8013 b1e135398
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e8013 b1e135398
      have b1e135560 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b1e135474
      have b1e135601 : x = (M.op x x) := by
        first
        | (have i₁ := b1e135560
           have i₂ := b1e123570
           grind)
        | exact superpose b1e123570 b1e135560
        | exact resolve b1e135560 b1e123570
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123570 b1e135560
      have b1e135722 : ∀ X0 : G, x = y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e134563 X0
           have i₂ := b1e135521
           grind)
        | exact superpose b1e135521 b1e134563
        | (have j0 := b1e134563 X0
           grind)
        | exact resolve b1e134563 b1e135521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e134563 b1e135521
      have b1e135808 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e135722 X0
           grind)
        | (have r₁ := b1e135722 X0
           have r₂ := b1e123869
           grind)
        | exact resolve b1e135722 b1e123869
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123869 b1e135722
      have b1e135952 : y = (k x (σ y)) := by
        first
        | (have i₁ := b1e103548 x x
           have i₂ := b1e135601
           grind)
        | exact superpose b1e135601 b1e103548
        | exact resolve b1e103548 b1e135601
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e103548 b1e135601
      have b1e135969 : y = (σ (k y y)) := by
        first
        | (have i₁ := b1e135952
           have i₂ := b1e123571 y
           grind)
        | exact superpose b1e123571 b1e135952
        | exact resolve b1e135952 b1e123571
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e123571 b1e135952
      have b1e136050 : y = (σ y) := by
        first
        | (have i₁ := b1e135969
           have i₂ := b1e135808 y
           grind)
        | exact superpose b1e135808 b1e135969
        | exact resolve b1e135969 b1e135808
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e135808 b1e135969
      have b1e136097 : False := by grind
      exact b1e136097
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
        intro X0 X1 X2 X3
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
      have b2e31 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ x) (σ y) X1
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e32 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
        intro X0 X1 X2 X3 X5
        first
        | (have i₁ := b2e10 X3 X2 (M.op X0 x) X5
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 X0 (M.op X1 X3) X0 X3
           have i₂ := b2e10 X0 X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e34 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X2) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b2e10 X2 X0 x X4
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 (M.op X1 x) X1 X2 x
           have i₂ := b2e10 (M.op X1 X2) X1 X2 x
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e36 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op (σ y) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 (σ x) X1 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e10
        | exact resolve b2e10 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e10 X3 X2 X4 (M.op X0 x)
           have i₂ := b2e10 X2 X0 x X1
           grind)
        | (have i₁ := b2e10 X0 (M.op X1 X3) X2 X0
           have i₂ := b2e10 X0 X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e10 X0 X1 X2 x
           have i₂ := b2e10 X0 X1 X3 x
           grind)
        | (have i₁ := b2e10 (M.op X1 X2) X1 X2 X3
           have i₂ := b2e10 (M.op X1 X3) X1 X2 X3
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e44 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e15 X2 (k (τ X0) X1)
           have i₂ := b2e25 X0 X1
           grind)
        | exact superpose b2e25 b2e15
        | exact resolve b2e15 b2e25
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b2e50 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e25 X0 X1
           have i₂ := b2e14 (τ X0) X1
           grind)
        | exact superpose b2e14 b2e25
        | (have j1 := b2e14 (τ X0) X1
           grind)
        | exact resolve b2e25 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e51 : x = (M.op x y) ∨ y = (M.op x y) := by
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
      have b2e54 : x = (M.op x y) := by
        first
        | (have r₁ := b2e51
           have r₂ := b2e17
           grind)
        | exact resolve b2e51 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e56 : (σ x) ≠ (σ y) := by
        first
        | (have i₁ := b2e19
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e19
        | exact resolve b2e19 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e57 : x ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e17
        | exact resolve b2e17 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 x X1 y
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e10
        | exact resolve b2e10 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e59 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op X0 x) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 X0 x y X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e10
        | exact resolve b2e10 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e67 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b2e70 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b2e31 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e31
        | exact resolve b2e31 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e167 : (σ y) = (M.op (σ y) (σ x)) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e70 (σ x)
           grind)
        | exact superpose b2e70 b2e18
        | exact resolve b2e18 b2e70
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e259 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e39 X0 (σ y) X1 (σ x)
           have i₂ := b2e167
           grind)
        | exact superpose b2e167 b2e39
        | exact resolve b2e39 b2e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e167
      have b2e296 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e32 x y X0 X2 X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e32
        | exact resolve b2e32 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e305 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ x) X2) X3) X4) = (M.op X4 (M.op (σ y) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e32 X0 X1 (M.op (σ x) X2) X4 X3
           have i₂ := b2e36 (M.op X0 X1) X2
           grind)
        | exact superpose b2e36 b2e32
        | exact resolve b2e32 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e345 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X5) X0) (M.op X2 X6)) := by
        intro X0 X1 X2 X3 X4 X5 X6
        first
        | (have i₁ := b2e10 (M.op (M.op X4 X5) X0) X2 X6 X3
           have i₂ := b2e32 X4 X5 X0 (M.op X2 X3) X1
           grind)
        | (have i₁ := b2e10 X3 X2 X2 X5
           have i₂ := b2e32 X0 X1 X2 X3 X5
           grind)
        | exact superpose b2e32 b2e10
        | exact resolve b2e10 b2e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e32
      have b2e356 : ∀ X2 X3 X4 : G, (M.op (M.op (M.op (σ x) X2) X3) X4) = (M.op X4 (σ y)) := by
        intro X2 X3 X4
        first
        | (have i₁ := b2e305 x x X2 X3 X4
           have i₂ := b2e259 X4 (M.op x x)
           grind)
        | exact superpose b2e259 b2e305
        | exact resolve b2e305 b2e259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e259 b2e305
      have b2e357 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e296 X0 X1 X2
           have i₂ := b2e58 X2 X0
           grind)
        | exact superpose b2e58 b2e296
        | exact resolve b2e296 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e296
      have b2e361 : ∀ X3 X4 : G, (M.op X4 (σ y)) = (M.op (M.op X3 (σ y)) X4) := by
        intro X3 X4
        first
        | (have i₁ := b2e356 x X3 X4
           have i₂ := b2e31 X3 x
           grind)
        | exact superpose b2e31 b2e356
        | exact resolve b2e356 b2e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e356
      have b2e362 : ∀ X4 : G, (M.op X4 (σ y)) = (M.op x X4) := by
        intro X4
        first
        | (have i₁ := b2e361 x X4
           have i₂ := b2e357 x (σ y) X4
           grind)
        | exact superpose b2e357 b2e361
        | exact resolve b2e361 b2e357
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e361
      have b2e370 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e70 X0
           have i₂ := b2e362 X0
           grind)
        | exact superpose b2e362 b2e70
        | exact resolve b2e70 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e70
      have b2e372 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X0 X2 (σ y)
           have i₂ := b2e362 X0
           grind)
        | exact superpose b2e362 b2e10
        | exact resolve b2e10 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e378 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e39 X1 X0 X2 (σ y)
           have i₂ := b2e362 X0
           grind)
        | exact superpose b2e362 b2e39
        | exact resolve b2e39 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e385 : (σ y) = (M.op x (σ x)) := by
        first
        | (have i₁ := b2e18
           have i₂ := b2e362 (σ x)
           grind)
        | exact superpose b2e362 b2e18
        | exact resolve b2e18 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e387 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b2e31 X0 (σ y)
           have i₂ := b2e362 (σ x)
           grind)
        | exact superpose b2e362 b2e31
        | exact resolve b2e31 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e31
      have b2e388 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e387 X0
           have i₂ := b2e59 X0 (σ x)
           grind)
        | exact superpose b2e59 b2e387
        | exact resolve b2e387 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e387
      have b2e395 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e378 X0 X1 X2
           have i₂ := b2e58 X1 X0
           grind)
        | exact superpose b2e58 b2e378
        | exact resolve b2e378 b2e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58 b2e378
      have b2e399 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X1 (M.op X0 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e372 X0 X1 X2
           have i₂ := b2e59 X1 X0
           grind)
        | exact superpose b2e59 b2e372
        | exact resolve b2e372 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e372
      have b2e484 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X3 (M.op X2 X4)) = X3 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e13 X3 (M.op X2 X4)
           have i₂ := b2e37 X0 X1 X2 X3 X4
           grind)
        | (have i₁ := b2e13 (M.op (M.op X0 X1) X2) X3
           have i₂ := b2e37 X0 X1 X2 X3 X4
           grind)
        | exact superpose b2e37 b2e13
        | (have j0 := b2e13 X3 (M.op X2 X4)
           grind)
        | exact resolve b2e13 b2e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e37
      have b2e537 : ∀ X2 X3 X4 : G, (M.op X2 X4) ≠ (M.op x X3) ∨ (k X3 (M.op X2 X4)) = X3 := by
        intro X2 X3 X4
        first
        | (have i₁ := b2e484 x x X2 X3 X4
           have i₂ := b2e357 (M.op x x) X2 X3
           grind)
        | exact superpose b2e357 b2e484
        | (have j0 := b2e484 x x X2 X3 X4
           grind)
        | (have r₁ := b2e484 x x x X2 X2
           have r₂ := b2e357 (M.op x x) x X2
           grind)
        | exact resolve b2e484 b2e357
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e484
      have b2e606 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b2e34 x (σ x) X0 X1
           have i₂ := b2e385
           grind)
        | exact superpose b2e385 b2e34
        | exact resolve b2e34 b2e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e34
      have b2e614 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e606 X0 x
           have i₂ := b2e59 X0 x
           grind)
        | exact superpose b2e59 b2e606
        | exact resolve b2e606 b2e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e59 b2e606
      have b2e1497 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b2e362 X0
           have i₂ := b2e388 X0
           grind)
        | exact superpose b2e388 b2e362
        | exact resolve b2e362 b2e388
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e388
      have b2e2193 : x = (M.op y x) := by
        first
        | (have i₁ := b2e54
           have i₂ := b2e1497 y
           grind)
        | exact superpose b2e1497 b2e54
        | exact resolve b2e54 b2e1497
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2493 : x ≠ x ∨ y = (k y x) := by
        first
        | (have i₁ := b2e13 y x
           have i₂ := b2e2193
           grind)
        | exact superpose b2e2193 b2e13
        | (have j0 := b2e13 y x
           grind)
        | (have r₁ := b2e13 y x
           have r₂ := b2e2193
           grind)
        | exact resolve b2e13 b2e2193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2509 : y = (k y x) := by grind
      clear b2e2493
      have b2e2660 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k X0 y)) ∨ (σ y) = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e49 X0 y
           have i₂ := b2e362 (σ X0)
           grind)
        | exact superpose b2e362 b2e49
        | exact resolve b2e49 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2685 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b2e39 X2 (σ X0) X3 (σ X1)
           have i₂ := b2e49 X0 X1
           grind)
        | exact superpose b2e49 b2e39
        | (have j1 := b2e49 X0 X1
           grind)
        | exact resolve b2e39 b2e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e39
      have b2e2693 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b2e49 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e2699 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e2685 X0 X1 X2 x
           have i₂ := b2e395 (σ X0) X2 x
           grind)
        | exact superpose b2e395 b2e2685
        | (have j0 := b2e2685 X0 X1 X2 x
           grind)
        | exact resolve b2e2685 b2e395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2685
      have b2e2749 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46 X1 (τ X0)
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e46
        | exact resolve b2e46 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e2754 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46 X0 X1
           have i₂ := b2e14 X0 (σ X1)
           grind)
        | exact superpose b2e14 b2e46
        | (have j1 := b2e14 X0 (σ X1)
           grind)
        | exact resolve b2e46 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16355 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 := by
        intro X0
        first
        | (have j0 := b2e537 x X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e537
      have b2e16399 : ∀ X0 : G, (k X0 (M.op X0 x)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e16355 X0
           have i₂ := b2e1497 X0
           grind)
        | (have i₁ := b2e16355 x
           have i₂ := b2e1497 x
           grind)
        | exact superpose b2e1497 b2e16355
        | exact resolve b2e16355 b2e1497
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16407 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e16355 (M.op X0 X1)
           have i₂ := b2e399 X0 x X1
           grind)
        | exact superpose b2e399 b2e16355
        | exact resolve b2e16355 b2e399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e399
      have b2e16427 : (σ y) = (k (σ y) (M.op x x)) := by
        first
        | (have i₁ := b2e16355 (σ y)
           have i₂ := b2e362 x
           grind)
        | exact superpose b2e362 b2e16355
        | exact resolve b2e16355 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16430 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x (σ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e67 X0 (M.op x (σ X0))
           have i₂ := b2e16355 (σ X0)
           grind)
        | exact superpose b2e16355 b2e67
        | exact resolve b2e67 b2e16355
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16431 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x (τ X0)))) := by
        intro X0
        first
        | (have i₁ := b2e25 X0 (M.op x (τ X0))
           have i₂ := b2e16355 (τ X0)
           grind)
        | exact superpose b2e16355 b2e25
        | exact resolve b2e25 b2e16355
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e16432 : ∀ X0 : G, (k X0 (σ (M.op x (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e16431 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e16431
        | exact resolve b2e16431 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16431
      have b2e16433 : ∀ X0 : G, (k X0 (τ (M.op x (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e16430 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e16430
        | exact resolve b2e16430 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16430
      have b2e16709 : (k y (τ (M.op x x))) = (τ (σ y)) := by
        first
        | (have i₁ := b2e67 y (M.op x x)
           have i₂ := b2e16427
           grind)
        | exact superpose b2e16427 b2e67
        | exact resolve b2e67 b2e16427
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16427
      have b2e16712 : y = (k y (τ (M.op x x))) := by
        first
        | (have i₁ := b2e16709
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e16709
        | exact resolve b2e16709 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16709
      have b2e16856 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op x (σ (σ X0)))))) := by
        intro X0
        first
        | (have i₁ := b2e67 X0 (τ (M.op x (σ (σ X0))))
           have i₂ := b2e16433 (σ X0)
           grind)
        | exact superpose b2e16433 b2e67
        | exact resolve b2e67 b2e16433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16433
      have b2e16861 : ∀ X0 : G, (k X0 (τ (τ (M.op x (σ (σ X0)))))) = X0 := by
        intro X0
        first
        | (have i₁ := b2e16856 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e16856
        | exact resolve b2e16856 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16856
      have b2e27659 : ∀ X0 : G, (σ X0) ≠ (σ (M.op x X0)) ∨ (σ (M.op x X0)) = (M.op (σ X0) (σ (M.op x X0))) := by
        intro X0
        first
        | (have i₁ := b2e2693 X0 (M.op x X0)
           have i₂ := b2e16355 X0
           grind)
        | exact superpose b2e16355 b2e2693
        | (have j0 := b2e2693 X0 (M.op x X0)
           grind)
        | exact resolve b2e2693 b2e16355
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27671 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e2693 (τ X0) (τ X1)
           have i₂ := b2e2749 X1 X0
           grind)
        | exact superpose b2e2749 b2e2693
        | (have j0 := b2e2693 (τ X0) (τ X1)
           grind)
        | exact resolve b2e2693 b2e2749
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27683 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e27671 X0 X1
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e27671
        | (have j0 := b2e27671 X0 X1
           grind)
        | exact resolve b2e27671 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27671
      have b2e27688 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b2e27683 X0 X1
           have i₂ := b2e12 X1
           grind)
        | exact superpose b2e12 b2e27683
        | (have j0 := b2e27683 X0 X1
           grind)
        | exact resolve b2e27683 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27683
      have b2e27692 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e27688 X0 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e27688
        | (have j0 := b2e27688 X0 X1
           grind)
        | exact resolve b2e27688 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27688
      have b2e27693 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b2e27692 X0 X1
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e27692
        | (have j0 := b2e27692 X0 X1
           grind)
        | exact resolve b2e27692 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27692
      have b2e27707 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e27693 (τ X0) (τ X1)
           have i₂ := b2e2749 X1 X0
           grind)
        | exact superpose b2e2749 b2e27693
        | (have j0 := b2e27693 (τ X0) (τ X1)
           grind)
        | exact resolve b2e27693 b2e2749
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e27727 : ∀ X0 X1 X2 : G, (σ (M.op x (τ X0))) = (k X0 (σ (M.op X1 X2))) ∨ (M.op X1 X2) = (M.op x (τ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e50 X0 (M.op X0 X2)
           have i₂ := b2e395 X0 (τ X0) X2
           grind)
        | exact superpose b2e395 b2e50
        | exact resolve b2e50 b2e395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e47180 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (σ (σ (k X0 X1)))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e2699 (σ X0) (σ X1) X2
           have i₂ := b2e15 X0 X1
           grind)
        | exact superpose b2e15 b2e2699
        | (have j0 := b2e2699 (σ X0) (σ X1) X2
           grind)
        | exact resolve b2e2699 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e47184 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e2699 (τ X0) (τ X1) X2
           have i₂ := b2e2749 X1 X0
           grind)
        | exact superpose b2e2749 b2e2699
        | (have j0 := b2e2699 (τ X0) (τ X1) X2
           grind)
        | exact resolve b2e2699 b2e2749
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2699 b2e2749
      have b2e47575 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e47184 X0 X1 X2
           have i₂ := b2e12 (k X0 X1)
           grind)
        | exact superpose b2e12 b2e47184
        | (have j0 := b2e47184 X0 X1 X2
           grind)
        | exact resolve b2e47184 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47184
      have b2e47683 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op x X2) = (M.op X2 (k X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e47575 X0 X0 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e47575
        | (have j0 := b2e47575 X0 X1 X2
           grind)
        | exact resolve b2e47575 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47575
      have b2e47745 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (k X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e47683 X0 X1 X2
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e47683
        | (have j0 := b2e47683 X0 X1 X2
           grind)
        | exact resolve b2e47683 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47683
      have b2e56842 : ∀ X0 X1 : G, (k (τ X1) (k X0 y)) = (τ (k X1 (M.op x (σ X0)))) ∨ (σ y) = (M.op x (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b2e46 X1 (k X0 y)
           have i₂ := b2e2660 X0
           grind)
        | exact superpose b2e2660 b2e46
        | (have j1 := b2e2660 X0
           grind)
        | exact resolve b2e46 b2e2660
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2660
      have b2e58438 : (τ (σ y)) = (k (τ x) x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b2e2754 x x
           have i₂ := b2e385
           grind)
        | exact superpose b2e385 b2e2754
        | exact resolve b2e2754 b2e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2754
      have b2e58465 : (τ (σ y)) = (k (τ x) x) := by
        first
        | (have r₁ := b2e58438
           have r₂ := b2e56
           grind)
        | exact resolve b2e58438 b2e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56 b2e58438
      have b2e58520 : y = (k (τ x) x) := by
        first
        | (have i₁ := b2e58465
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e58465
        | exact resolve b2e58465 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58465
      have b2e58633 : (σ y) = (k x (σ x)) := by
        first
        | (have i₁ := b2e25 x x
           have i₂ := b2e58520
           grind)
        | exact superpose b2e58520 b2e25
        | exact resolve b2e25 b2e58520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58634 : y = (M.op (τ x) x) ∨ x = (M.op (τ x) x) := by
        first
        | (have i₁ := b2e14 (τ x) x
           have i₂ := b2e58520
           grind)
        | exact superpose b2e58520 b2e14
        | (have j0 := b2e14 (τ x) x
           grind)
        | exact resolve b2e14 b2e58520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e58651 : y = (M.op x (τ x)) ∨ x = (M.op (τ x) x) := by
        first
        | (have i₁ := b2e58634
           have i₂ := b2e1497 (τ x)
           grind)
        | exact superpose b2e1497 b2e58634
        | exact resolve b2e58634 b2e1497
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58634
      have b2e58657 : x = (M.op x (τ x)) ∨ y = (M.op x (τ x)) := by
        first
        | (have i₁ := b2e58651
           have i₂ := b2e1497 (τ x)
           grind)
        | exact superpose b2e1497 b2e58651
        | exact resolve b2e58651 b2e1497
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e1497 b2e58651
      have b2e59867 : x = (k x (σ x)) ∨ y = (M.op x (τ x)) := by
        first
        | (have i₁ := b2e16432 x
           have i₂ := b2e58657
           grind)
        | exact superpose b2e58657 b2e16432
        | exact resolve b2e16432 b2e58657
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16432
      have b2e59877 : (τ x) = (k (τ x) x) ∨ y = (M.op x (τ x)) := by
        first
        | (have i₁ := b2e16355 (τ x)
           have i₂ := b2e58657
           grind)
        | exact superpose b2e58657 b2e16355
        | exact resolve b2e16355 b2e58657
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16355 b2e58657
      have b2e60001 : y = (M.op x (τ x)) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e59877
           have i₂ := b2e58520
           grind)
        | exact superpose b2e58520 b2e59877
        | exact resolve b2e59877 b2e58520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58520 b2e59877
      have b2e60003 : y = (M.op x (τ x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e59867
           have i₂ := b2e58633
           grind)
        | exact superpose b2e58633 b2e59867
        | exact resolve b2e59867 b2e58633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e58633 b2e59867
      have b2e60210 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (τ x) := by
        intro X0
        first
        | (have i₁ := b2e357 x (τ x) X0
           have i₂ := b2e60001
           grind)
        | exact superpose b2e60001 b2e357
        | exact resolve b2e357 b2e60001
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60001
      have b2e60604 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (σ y) := by
        intro X0
        first
        | (have i₁ := b2e357 x (τ x) X0
           have i₂ := b2e60003
           grind)
        | exact superpose b2e60003 b2e357
        | exact resolve b2e357 b2e60003
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60003
      have b2e61770 : x = (k x (M.op y x)) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e16399 x
           have i₂ := b2e60210 x
           grind)
        | exact superpose b2e60210 b2e16399
        | exact resolve b2e16399 b2e60210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e60210
      have b2e61773 : x = (k x x) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e61770
           have i₂ := b2e2193
           grind)
        | exact superpose b2e2193 b2e61770
        | exact resolve b2e61770 b2e2193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e61770
      have b2e62767 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e2693 x x
           have i₂ := b2e61773
           grind)
        | exact superpose b2e61773 b2e2693
        | (have j0 := b2e2693 x x
           grind)
        | exact resolve b2e2693 b2e61773
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2693 b2e61773
      have b2e62777 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (τ x) := by grind
      clear b2e62767
      have b2e68404 : x = (k x (M.op y x)) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e16399 x
           have i₂ := b2e60604 x
           grind)
        | exact superpose b2e60604 b2e16399
        | exact resolve b2e16399 b2e60604
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16399 b2e60604
      have b2e68408 : x = (k x x) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e68404
           have i₂ := b2e2193
           grind)
        | exact superpose b2e2193 b2e68404
        | exact resolve b2e68404 b2e2193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e68404
      have b2e69783 : x ≠ x ∨ x = (M.op x x) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e27693 x x
           have i₂ := b2e68408
           grind)
        | exact superpose b2e68408 b2e27693
        | (have j0 := b2e27693 x x
           grind)
        | (have r₁ := b2e27693 x x
           have r₂ := b2e68408
           grind)
        | exact resolve b2e27693 b2e68408
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27693 b2e68408
      have b2e69788 : x = (M.op x x) ∨ x = (σ y) := by grind
      clear b2e69783
      have b2e71991 : ∀ X0 X1 X2 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op x X2) = (M.op X2 (σ (σ (k X1 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e13 (σ (σ X1)) (σ (σ X0))
           have i₂ := b2e47180 X1 X0 X2
           grind)
        | exact superpose b2e47180 b2e13
        | (have j0 := b2e13 (σ (σ X1)) (σ (σ X0))
           have j1 := b2e47180 X1 X0 X2
           grind)
        | (have r₁ := b2e13 (σ (σ X0)) (σ (σ X1))
           have r₂ := b2e47180 X0 X1 X2
           grind)
        | exact resolve b2e13 b2e47180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47180
      have b2e72075 : ∀ X0 X1 X2 : G, (σ (σ X1)) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op x X2) = (M.op X2 (σ (σ (k X1 X0)))) := by
        intro X0 X1 X2
        first
        | (have j0 := b2e71991 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e71991
      have b2e72141 : ∀ X0 X1 X2 : G, (σ (σ X1)) = (σ (k (σ X1) (σ X0))) ∨ (M.op x X2) = (M.op X2 (σ (σ (k X1 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e72075 X0 X1 X2
           have i₂ := b2e15 (σ X1) (σ X0)
           grind)
        | exact superpose b2e15 b2e72075
        | (have j0 := b2e72075 X0 X1 X2
           grind)
        | exact resolve b2e72075 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e72075
      have b2e72393 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X2 (σ (σ (k X1 X0)))) ∨ (σ (σ X1)) = (σ (σ (k X1 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e72141 X0 X1 X2
           have i₂ := b2e15 X1 X0
           grind)
        | exact superpose b2e15 b2e72141
        | (have j0 := b2e72141 X0 X1 X2
           grind)
        | exact resolve b2e72141 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e72141
      have b2e89497 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (σ x) X2)) = (M.op (M.op (M.op X3 X4) X0) (σ x)) ∨ y = (τ x) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b2e345 X0 X1 (σ x) X2 X3 X4 (σ x)
           have i₂ := b2e62777
           grind)
        | exact superpose b2e62777 b2e345
        | exact resolve b2e345 b2e62777
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e345 b2e62777
      have b2e89513 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) X2)) = (M.op x (σ x)) ∨ y = (τ x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e89497 X0 X1 X2 x x
           have i₂ := b2e357 (M.op x x) X0 (σ x)
           grind)
        | exact superpose b2e357 b2e89497
        | exact resolve b2e89497 b2e357
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e89497
      have b2e89574 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 X1) (M.op (σ x) X2)) ∨ y = (τ x) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e89513 X0 X1 X2
           have i₂ := b2e385
           grind)
        | exact superpose b2e385 b2e89513
        | exact resolve b2e89513 b2e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e89513
      have b2e89618 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 X1)) ∨ y = (τ x) := by
        intro X0 X1
        first
        | (have i₁ := b2e89574 X0 X1 x
           have i₂ := b2e36 (M.op X0 X1) x
           grind)
        | exact superpose b2e36 b2e89574
        | exact resolve b2e89574 b2e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e36 b2e89574
      have b2e89643 : ∀ X0 X1 : G, (σ y) = (M.op x (M.op X0 X1)) ∨ y = (τ x) := by
        intro X0 X1
        first
        | (have i₁ := b2e89618 X0 X1
           have i₂ := b2e370 (M.op X0 X1)
           grind)
        | exact superpose b2e370 b2e89618
        | exact resolve b2e89618 b2e370
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e370 b2e89618
      have b2e89667 : (σ y) = (M.op x x) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e89643 x x
           have i₂ := b2e395 x x x
           grind)
        | exact superpose b2e395 b2e89643
        | exact resolve b2e89643 b2e395
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e395 b2e89643
      have b2e90131 : x = (σ y) ∨ x = (σ y) ∨ y = (τ x) := by
        first
        | (have i₁ := b2e69788
           have i₂ := b2e89667
           grind)
        | exact superpose b2e89667 b2e69788
        | exact resolve b2e69788 b2e89667
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e69788 b2e89667
      have b2e90254 : y = (τ x) ∨ x = (σ y) := by grind
      clear b2e90131
      have b2e90890 : x = (σ y) ∨ x = (σ y) := by
        first
        | (have i₁ := b2e12 x
           have i₂ := b2e90254
           grind)
        | exact superpose b2e90254 b2e12
        | exact resolve b2e12 b2e90254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e90254
      have b2e90966 : x = (σ y) := by grind
      clear b2e90890
      have b2e91455 : y = (τ x) := by
        first
        | (have i₁ := b2e11 y
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e11
        | exact resolve b2e11 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e91456 : ∀ X0 : G, (σ (k y X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e15 y X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e15
        | exact resolve b2e15 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e91458 : ∀ X0 X1 : G, (σ (k X0 (k (τ X1) y))) = (k (σ X0) (k X1 x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e44 X1 y X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e44
        | exact resolve b2e44 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e91462 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 x)) := by
        intro X0
        first
        | (have i₁ := b2e46 X0 y
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e46
        | exact resolve b2e46 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e91469 : ∀ X0 : G, (k y (τ X0)) = (τ (k x X0)) := by
        intro X0
        first
        | (have i₁ := b2e67 y X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e67
        | exact resolve b2e67 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e67
      have b2e91484 : y = (k y (τ (τ (M.op x (σ x))))) := by
        first
        | (have i₁ := b2e16861 y
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e16861
        | exact resolve b2e16861 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16861
      have b2e91511 : y = (k y (τ (τ (σ y)))) := by
        first
        | (have i₁ := b2e91484
           have i₂ := b2e385
           grind)
        | exact superpose b2e385 b2e91484
        | exact resolve b2e91484 b2e385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e385 b2e91484
      have b2e91528 : y = (k y (τ y)) := by
        first
        | (have i₁ := b2e91511
           have i₂ := b2e11 y
           grind)
        | exact superpose b2e11 b2e91511
        | exact resolve b2e91511 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e91511
      have b2e93268 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) ∨ (τ y) = (M.op y (τ y)) := by
        intro X0
        first
        | (have i₁ := b2e47745 y (τ y) X0
           have i₂ := b2e91528
           grind)
        | exact superpose b2e91528 b2e47745
        | (have j0 := b2e47745 y (τ y) x
           grind)
        | exact resolve b2e47745 b2e91528
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47745 b2e91528
      have b2e97419 : (τ y) = (k (τ y) y) := by
        first
        | (have i₁ := b2e91462 y
           have i₂ := b2e2509
           grind)
        | exact superpose b2e2509 b2e91462
        | exact resolve b2e91462 b2e2509
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2509 b2e91462
      have b2e97950 : (τ y) = (M.op (τ y) y) ∨ y = (M.op (τ y) y) := by
        first
        | (have i₁ := b2e14 (τ y) y
           have i₂ := b2e97419
           grind)
        | exact superpose b2e97419 b2e14
        | (have j0 := b2e14 (τ y) y
           grind)
        | exact resolve b2e14 b2e97419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e97419
      have b2e155235 : (M.op x (σ y)) = (M.op y x) ∨ (τ y) = (M.op y (τ y)) := by
        first
        | (have i₁ := b2e614 y
           have i₂ := b2e93268 (σ y)
           grind)
        | exact superpose b2e93268 b2e614
        | exact resolve b2e614 b2e93268
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e614 b2e93268
      have b2e155400 : x = (M.op x (σ y)) ∨ (τ y) = (M.op y (τ y)) := by
        first
        | (have i₁ := b2e155235
           have i₂ := b2e2193
           grind)
        | exact superpose b2e2193 b2e155235
        | exact resolve b2e155235 b2e2193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e2193 b2e155235
      have b2e155644 : (τ y) = (M.op y (τ y)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e155400
           have i₂ := b2e362 x
           grind)
        | (have i₁ := b2e155400
           have i₂ := b2e362 (σ y)
           grind)
        | exact superpose b2e362 b2e155400
        | exact resolve b2e155400 b2e362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e362 b2e155400
      have b2e156436 : ∀ X0 : G, (M.op x X0) = (M.op (τ y) X0) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e357 y (τ y) X0
           have i₂ := b2e155644
           grind)
        | exact superpose b2e155644 b2e357
        | exact resolve b2e357 b2e155644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e155644
      have b2e157395 : (M.op x y) = (τ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e97950
           have i₂ := b2e156436 y
           grind)
        | exact superpose b2e156436 b2e97950
        | exact resolve b2e97950 b2e156436
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e97950 b2e156436
      have b2e157694 : (M.op x y) = (τ y) ∨ x = (M.op x x) := by
        first
        | (have r₁ := b2e157395
           have r₂ := b2e17
           grind)
        | exact resolve b2e157395 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e157395
      have b2e157802 : x = (M.op x x) ∨ x = (τ y) := by
        first
        | (have i₁ := b2e157694
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e157694
        | exact resolve b2e157694 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e157694
      have b2e158185 : x = (k x x) ∨ x = (τ y) := by
        first
        | (have i₁ := b2e16407 x x
           have i₂ := b2e157802
           grind)
        | exact superpose b2e157802 b2e16407
        | exact resolve b2e16407 b2e157802
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16407 b2e157802
      have b2e158988 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ x = (τ y) := by
        first
        | (have i₁ := b2e27707 x x
           have i₂ := b2e158185
           grind)
        | exact superpose b2e158185 b2e27707
        | (have j0 := b2e27707 x x
           grind)
        | exact resolve b2e27707 b2e158185
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27707 b2e158185
      have b2e159001 : (τ x) = (M.op (τ x) (τ x)) ∨ x = (τ y) := by grind
      clear b2e158988
      have b2e159013 : y = (M.op y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b2e159001
           have i₂ := b2e91455
           grind)
        | exact superpose b2e91455 b2e159001
        | exact resolve b2e159001 b2e91455
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e159001
      have b2e161502 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (τ y) := by
        intro X0
        first
        | (have i₁ := b2e357 y y X0
           have i₂ := b2e159013
           grind)
        | exact superpose b2e159013 b2e357
        | exact resolve b2e357 b2e159013
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e357
      have b2e162347 : y ≠ (M.op y y) ∨ x = (τ y) := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e161502 y
           grind)
        | exact superpose b2e161502 b2e17
        | exact resolve b2e17 b2e161502
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e161502
      have b2e162637 : x = (τ y) := by
        first
        | (have r₁ := b2e162347
           have r₂ := b2e159013
           grind)
        | exact resolve b2e162347 b2e159013
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e159013 b2e162347
      have b2e162964 : y = (σ x) := by
        first
        | (have i₁ := b2e12 y
           have i₂ := b2e162637
           grind)
        | exact superpose b2e162637 b2e12
        | exact resolve b2e12 b2e162637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e162965 : ∀ X0 : G, (σ (k x X0)) = (k y (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e25 y X0
           have i₂ := b2e162637
           grind)
        | exact superpose b2e162637 b2e25
        | exact resolve b2e25 b2e162637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e25
      have b2e164060 : (k y y) = (σ (k x x)) := by
        first
        | (have i₁ := b2e162965 x
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e162965
        | exact resolve b2e162965 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e162965
      have b2e164319 : (σ (k y (k x x))) = (k x (k y y)) := by
        first
        | (have i₁ := b2e91456 (k x x)
           have i₂ := b2e164060
           grind)
        | exact superpose b2e164060 b2e91456
        | exact resolve b2e91456 b2e164060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e91456 b2e164060
      have b2e167989 : ∀ X0 X1 : G, (τ (σ (M.op x (τ x)))) = (k y (τ (σ (M.op X0 X1)))) ∨ (M.op X0 X1) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e91469 (σ (M.op X0 X1))
           have i₂ := b2e27727 x X0 X1
           grind)
        | exact superpose b2e27727 b2e91469
        | (have j1 := b2e27727 x X0 X1
           grind)
        | exact resolve b2e91469 b2e27727
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27727 b2e91469
      have b2e167996 : ∀ X0 X1 : G, (k y (M.op X0 X1)) = (τ (σ (M.op x (τ x)))) ∨ (M.op X0 X1) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e167989 X0 X1
           have i₂ := b2e11 (M.op X0 X1)
           grind)
        | exact superpose b2e11 b2e167989
        | (have j0 := b2e167989 X0 X1
           grind)
        | exact resolve b2e167989 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e167989
      have b2e168020 : ∀ X0 X1 : G, (k y (M.op X0 X1)) = (M.op x (τ x)) ∨ (M.op X0 X1) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e167996 X0 X1
           have i₂ := b2e11 (M.op x (τ x))
           grind)
        | exact superpose b2e11 b2e167996
        | (have j0 := b2e167996 X0 X1
           grind)
        | exact resolve b2e167996 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e167996
      have b2e168037 : ∀ X0 X1 : G, (M.op x y) = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e168020 X0 X1
           have i₂ := b2e91455
           grind)
        | exact superpose b2e91455 b2e168020
        | (have j0 := b2e168020 X0 X1
           grind)
        | exact resolve b2e168020 b2e91455
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168020
      have b2e168045 : ∀ X0 X1 : G, x = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op x (τ x)) := by
        intro X0 X1
        first
        | (have i₁ := b2e168037 X0 X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e168037
        | (have j0 := b2e168037 X0 X1
           grind)
        | exact resolve b2e168037 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168037
      have b2e168052 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x y) ∨ x = (k y (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b2e168045 X0 X1
           have i₂ := b2e91455
           grind)
        | exact superpose b2e91455 b2e168045
        | (have j0 := b2e168045 X0 X1
           grind)
        | exact resolve b2e168045 b2e91455
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168045
      have b2e168055 : ∀ X0 X1 : G, x = (k y (M.op X0 X1)) ∨ (M.op X0 X1) = x := by
        intro X0 X1
        first
        | (have i₁ := b2e168052 X0 X1
           have i₂ := b2e54
           grind)
        | exact superpose b2e54 b2e168052
        | (have j0 := b2e168052 X0 X1
           grind)
        | exact resolve b2e168052 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168052
      have b2e183724 : ∀ X0 : G, (τ x) = (k (τ y) (k X0 y)) ∨ (σ y) = (M.op x (σ X0)) ∨ x = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e56842 X0 y
           have i₂ := b2e168055 x (σ X0)
           grind)
        | exact superpose b2e168055 b2e56842
        | (have j0 := b2e56842 X0 x
           have j1 := b2e168055 x (σ X0)
           grind)
        | exact resolve b2e56842 b2e168055
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e56842
      have b2e183739 : ∀ X0 : G, (τ x) = (k x (k X0 y)) ∨ (σ y) = (M.op x (σ X0)) ∨ x = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e183724 X0
           have i₂ := b2e162637
           grind)
        | exact superpose b2e162637 b2e183724
        | (have j0 := b2e183724 X0
           grind)
        | exact resolve b2e183724 b2e162637
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e162637 b2e183724
      have b2e183752 : ∀ X0 : G, y = (k x (k X0 y)) ∨ (σ y) = (M.op x (σ X0)) ∨ x = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e183739 X0
           have i₂ := b2e91455
           grind)
        | exact superpose b2e91455 b2e183739
        | (have j0 := b2e183739 X0
           grind)
        | exact resolve b2e183739 b2e91455
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183739
      have b2e183756 : ∀ X0 : G, x = (M.op x (σ X0)) ∨ y = (k x (k X0 y)) ∨ x = (M.op x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b2e183752 X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e183752
        | (have j0 := b2e183752 X0
           grind)
        | exact resolve b2e183752 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183752
      have b2e183757 : ∀ X0 : G, y = (k x (k X0 y)) ∨ x = (M.op x (σ X0)) := by
        intro X0
        first
        | (have j0 := b2e183756 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183756
      have b2e183795 : ∀ X0 : G, (σ y) = (k (σ x) (k X0 x)) ∨ x = (M.op x (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e91458 x X0
           have i₂ := b2e183757 (τ X0)
           grind)
        | exact superpose b2e183757 b2e91458
        | (have j1 := b2e183757 (τ X0)
           grind)
        | exact resolve b2e91458 b2e183757
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e91458 b2e183757
      have b2e183812 : ∀ X0 : G, (σ y) = (k y (k X0 x)) ∨ x = (M.op x (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e183795 X0
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e183795
        | (have j0 := b2e183795 X0
           grind)
        | exact resolve b2e183795 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183795
      have b2e183829 : ∀ X0 : G, x = (k y (k X0 x)) ∨ x = (M.op x (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b2e183812 X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e183812
        | (have j0 := b2e183812 X0
           grind)
        | exact resolve b2e183812 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183812
      have b2e183840 : ∀ X0 : G, x = (k y (k X0 x)) ∨ x = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b2e183829 X0
           have i₂ := b2e12 X0
           grind)
        | exact superpose b2e12 b2e183829
        | (have j0 := b2e183829 X0
           grind)
        | exact resolve b2e183829 b2e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183829
      have b2e183940 : (σ x) = (k x (k y y)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e164319
           have i₂ := b2e183840 x
           grind)
        | exact superpose b2e183840 b2e164319
        | (have j1 := b2e183840 x
           grind)
        | exact resolve b2e164319 b2e183840
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e164319 b2e183840
      have b2e183972 : y = (k x (k y y)) ∨ x = (M.op x x) := by
        first
        | (have i₁ := b2e183940
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e183940
        | exact resolve b2e183940 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e183940
      have b2e184142 : ∀ X0 : G, (M.op x X0) = (M.op X0 (σ (σ y))) ∨ (σ (σ x)) = (σ (σ y)) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e72393 (k y y) x x
           have i₂ := b2e183972
           grind)
        | exact superpose b2e183972 b2e72393
        | exact resolve b2e72393 b2e183972
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e72393 b2e183972
      have b2e184143 : ∀ X0 : G, (M.op x X0) = (M.op X0 (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e184142 X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e184142
        | exact resolve b2e184142 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e184142
      have b2e184153 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) ∨ (σ (σ x)) = (σ (σ y)) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e184143 X0
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e184143
        | exact resolve b2e184143 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e184143
      have b2e184159 : ∀ X0 : G, (σ x) = (σ (σ x)) ∨ (M.op x X0) = (M.op X0 y) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e184153 X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e184153
        | (have j0 := b2e184153 X0
           grind)
        | exact resolve b2e184153 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e184153
      have b2e184160 : ∀ X0 : G, y = (σ y) ∨ (M.op x X0) = (M.op X0 y) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e184159 X0
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e184159
        | (have j0 := b2e184159 X0
           grind)
        | exact resolve b2e184159 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e184159
      have b2e184161 : ∀ X0 : G, x = y ∨ (M.op x X0) = (M.op X0 y) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b2e184160 X0
           have i₂ := b2e90966
           grind)
        | exact superpose b2e90966 b2e184160
        | (have j0 := b2e184160 X0
           grind)
        | exact resolve b2e184160 b2e90966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e90966 b2e184160
      have b2e184162 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b2e184161 X0
           grind)
        | (have r₁ := b2e184161 X0
           have r₂ := b2e57
           grind)
        | exact resolve b2e184161 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e184161
      have b2e184804 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
      clear b2e184162
      have b2e184827 : x = (M.op x x) := by
        first
        | (have r₁ := b2e184804
           have r₂ := b2e54
           grind)
        | exact resolve b2e184804 b2e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e54 b2e184804
      have b2e185305 : y = (k y (τ x)) := by
        first
        | (have i₁ := b2e16712
           have i₂ := b2e184827
           grind)
        | exact superpose b2e184827 b2e16712
        | exact resolve b2e16712 b2e184827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e16712
      have b2e185333 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b2e27659 x
           have i₂ := b2e184827
           grind)
        | exact superpose b2e184827 b2e27659
        | exact resolve b2e27659 b2e184827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27659 b2e184827
      have b2e185463 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b2e185333
      have b2e185521 : y = (M.op y y) := by
        first
        | (have i₁ := b2e185463
           have i₂ := b2e162964
           grind)
        | exact superpose b2e162964 b2e185463
        | exact resolve b2e185463 b2e162964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e162964 b2e185463
      have b2e185530 : y = (k y y) := by
        first
        | (have i₁ := b2e185305
           have i₂ := b2e91455
           grind)
        | exact superpose b2e91455 b2e185305
        | exact resolve b2e185305 b2e91455
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e91455 b2e185305
      have b2e185945 : x = (k y y) ∨ x = y := by
        first
        | (have i₁ := b2e168055 y y
           have i₂ := b2e185521
           grind)
        | exact superpose b2e185521 b2e168055
        | exact resolve b2e168055 b2e185521
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168055 b2e185521
      have b2e185959 : x = (k y y) := by
        first
        | (have r₁ := b2e185945
           have r₂ := b2e57
           grind)
        | exact resolve b2e185945 b2e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e185945
      have b2e186019 : x = y := by
        first
        | (have i₁ := b2e185959
           have i₂ := b2e185530
           grind)
        | exact superpose b2e185530 b2e185959
        | exact resolve b2e185959 b2e185530
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e185530 b2e185959
      have b2e186054 : False := by grind
      exact b2e186054
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
      have b3e36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b3e2121 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e36 x y
           grind)
        | exact superpose b3e36 b3e16
        | (have j1 := b3e36 x y
           grind)
        | exact resolve b3e16 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36
      have b3e2158 : (σ (M.op x y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b3e2121
           have r₂ := b3e18
           grind)
        | exact resolve b3e2121 b3e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2121
      have b3e2161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b3e2158
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2158
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2158 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2158
      have b3e2162 : y = (M.op x y) := by grind
      clear b3e2161
      have b3e2163 : False := by grind
      exact b3e2163
