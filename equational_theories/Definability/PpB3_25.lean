import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq65 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq68 (M.op X0 X1)
       grind)
    | exact superpose eq68 eq23
    | exact resolve eq23 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq23
    | exact resolve eq23 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq197 X0 X1
       grind)
    | exact superpose eq197 eq9
    | (have j1 := eq197 X0 X1
       grind)
    | exact resolve eq9 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq197 X0 X0
       grind)
    | exact superpose eq197 eq68
    | (have j1 := eq197 X0 X0
       grind)
    | exact resolve eq68 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq287 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq197 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq288 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq291 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq370 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq288 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq288
    | (have j0 := eq288 (τ X0)
       grind)
    | exact resolve eq288 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq288
  have eq372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | (have j0 := eq370 X0
       grind)
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq375 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372
    | (have j0 := eq372 X0
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq479 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1277 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq291
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1312 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1277 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1277
    | (have j0 := eq1277 X0
       grind)
    | exact resolve eq1277 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1277
  have eq1316 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1312 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1312
    | (have j0 := eq1312 X0
       grind)
    | exact resolve eq1312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq2544 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X1) X0) X7)) X8) X1) X8) = X8 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq70 X1 (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X0 X7 X8
       have i₂ := eq65 X0 X2 X3 X4 X5 X6
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq70
  have eq5529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq269
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq269
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq269 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq5532 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq5529
  have eq5932 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq270 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq270
    | (have j0 := eq270 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq270 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq6047 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5932 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5932
    | (have j0 := eq5932 X0 X1 X2
       grind)
    | exact resolve eq5932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932
  have eq6054 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6047 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6047
    | (have j0 := eq6047 X0 X1 X2
       grind)
    | exact resolve eq6047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047
  have eq6060 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6054 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6054
    | (have j0 := eq6054 X0 X1 X2
       grind)
    | exact resolve eq6054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6054
  have eq6065 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6060 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6060
    | (have j0 := eq6060 X0 X1 X2
       grind)
    | exact resolve eq6060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060
  have eq6070 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6065 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6065
    | (have j0 := eq6065 (σ (τ X1)) X1 X2
       grind)
    | exact resolve eq6065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6065
  have eq6075 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6070 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6070
    | (have j0 := eq6070 X0 X1 X2
       grind)
    | exact resolve eq6070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq17896 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (k X1 X0) X1 X0
       have i₂ := eq6075 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6075 eq87
    | (have j1 := eq6075 X1 X0 x
       grind)
    | exact resolve eq87 eq6075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq6075
  have eq40998 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5532
       grind)
    | exact superpose eq5532 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5532
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5532
       grind)
    | exact resolve eq12 eq5532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5532
  have eq41130 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq40998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40998
  have eq55962 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17896 X0 X0
       have i₂ := eq1316 X0
       grind)
    | exact superpose eq1316 eq17896
    | (have j0 := eq17896 X0 X0
       have j1 := eq1316 X0
       grind)
    | exact resolve eq17896 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq17896
  have eq56168 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq55962 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55962
  have eq56190 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56168 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq56168
    | (have j0 := eq56168 (σ X0)
       grind)
    | exact resolve eq56168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56196 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56168 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq56168
    | (have j0 := eq56168 (τ X0)
       grind)
    | exact resolve eq56168 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq56168
  have eq329841 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq107 (σ y) (σ x)
       have i₂ := eq41130 X0
       grind)
    | exact superpose eq41130 eq107
    | (have j0 := eq107 (σ y) x
       have j1 := eq41130 (σ y)
       grind)
    | (have r₁ := eq107 (σ y) (σ x)
       have r₂ := eq41130 X0
       grind)
    | (have r₁ := eq107 y x
       have r₂ := eq41130 X0
       grind)
    | (have r₁ := eq107 y y
       have r₂ := eq41130 X0
       grind)
    | exact resolve eq107 eq41130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq41130
  have eq330122 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq329841 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329841
  have eq330123 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq330122 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330122
  have eq330268 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq375 (σ y)
       grind)
    | (have r₁ := eq330123
       have r₂ := eq375 (σ y)
       grind)
    | exact resolve eq330123 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq330123
  have eq330327 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq330268
       grind)
    | exact superpose eq330268 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq330268
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq330268
       grind)
    | exact resolve eq12 eq330268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330268
  have eq330607 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq330327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330327
  have eq330865 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq56196 (σ y)
       have i₂ := eq330607 (σ y)
       grind)
    | exact superpose eq330607 eq56196
    | (have j0 := eq56196 (σ y)
       grind)
    | exact resolve eq56196 eq330607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56196 eq330607
  have eq331296 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq330865
  have eq331393 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq331296
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq331296
    | exact resolve eq331296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331296
  have eq331394 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq331393
  have eq331509 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq331394
       grind)
    | exact superpose eq331394 eq76
    | exact resolve eq76 eq331394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331601 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq479 y y x
       have i₂ := eq331394
       grind)
    | exact superpose eq331394 eq479
    | exact resolve eq479 eq331394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331394
  have eq331850 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq331601 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq331601
    | exact resolve eq331601 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331601
  have eq342831 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq331509 X0
       have i₂ := eq331850 X0
       grind)
    | exact superpose eq331850 eq331509
    | exact resolve eq331509 eq331850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331509 eq331850
  have eq343328 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq342831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342831
  have eq343386 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 y x
       have i₂ := eq343328 X0
       grind)
    | exact superpose eq343328 eq90
    | (have j1 := eq343328 y
       grind)
    | exact resolve eq90 eq343328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343328
  have eq343759 : y = (M.op y y) := by
    first
    | (have j0 := eq343386 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343386
  have eq343882 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq343759
       grind)
    | exact superpose eq343759 eq12
    | (have r₁ := eq12 X0 y
       have r₂ := eq343759
       grind)
    | exact resolve eq12 eq343759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343887 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq343759
       grind)
    | exact superpose eq343759 eq76
    | exact resolve eq76 eq343759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq343979 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq479 y y x
       have i₂ := eq343759
       grind)
    | exact superpose eq343759 eq479
    | exact resolve eq479 eq343759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344172 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq343882 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343882
  have eq344243 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq343979 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq343979
    | exact resolve eq343979 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq343979
  have eq344401 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq56190 y
       have i₂ := eq344172 y
       grind)
    | exact superpose eq344172 eq56190
    | (have j0 := eq56190 y
       grind)
    | exact resolve eq56190 eq344172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56190 eq344172
  have eq344824 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq344401
  have eq352464 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq343887 X0
       have i₂ := eq344243 X0
       grind)
    | exact superpose eq344243 eq343887
    | exact resolve eq343887 eq344243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343887
  have eq352466 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq344243 X0
       have i₂ := eq352464 X0
       grind)
    | exact superpose eq352464 eq344243
    | exact resolve eq344243 eq352464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344243
  have eq352570 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq479 y X1 X0
       have i₂ := eq352464 X0
       grind)
    | exact superpose eq352464 eq479
    | exact resolve eq479 eq352464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq353546 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352570 X0 X0
       have i₂ := eq352464 X0
       grind)
    | exact superpose eq352464 eq352570
    | exact resolve eq352570 eq352464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352570
  have eq360342 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op y X1)) X2)) X3)) X4)) X0) y) X5)) X6) X0) X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2544 y X0 y X1 X2 X3 X4 X5 X6
       have i₂ := eq343759
       grind)
    | exact superpose eq343759 eq2544
    | exact resolve eq2544 eq343759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544 eq343759
  have eq361292 : ∀ X0 X5 X6 : G, (M.op (M.op (M.op (M.op X0 (M.op y X5)) X6) X0) X6) = X6 := by
    intro X0 X5 X6
    first
    | (have i₁ := eq360342 X0 x x x x X5 X6
       have i₂ := eq352466 (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op (M.op y (M.op y x)) x)) x)) x)) X0)
       grind)
    | exact superpose eq352466 eq360342
    | exact resolve eq360342 eq352466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360342
  have eq361320 : ∀ X0 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X5) X6) X0) X6) = X6 := by
    intro X0 X5 X6
    first
    | (have i₁ := eq361292 X0 X5 X6
       have i₂ := eq352464 X5
       grind)
    | exact superpose eq352464 eq361292
    | exact resolve eq361292 eq352464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352464 eq361292
  have eq391462 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq361320 (σ y) (σ y) X0
       have i₂ := eq344824
       grind)
    | exact superpose eq344824 eq361320
    | exact resolve eq361320 eq344824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344824 eq361320
  have eq392823 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391462 X0
       have i₂ := eq353546 X0 (σ y)
       grind)
    | exact superpose eq353546 eq391462
    | exact resolve eq391462 eq353546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391462
  have eq394498 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq353546 X0 (σ y)
       have i₂ := eq392823 X0
       grind)
    | exact superpose eq392823 eq353546
    | exact resolve eq353546 eq392823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353546 eq392823
  have eq399415 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq394498 (σ x)
       grind)
    | exact superpose eq394498 eq16
    | exact resolve eq16 eq394498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394498
  have eq399610 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq399415
       have i₂ := eq352466 x
       grind)
    | exact superpose eq352466 eq399415
    | exact resolve eq399415 eq352466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352466 eq399415
  have eq399611 : False := by grind
  exact eq399611

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq61
    | exact resolve eq61 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X0 X2 X3
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq62
    | exact resolve eq62 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq654 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq654
    | (have j0 := eq654 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq654 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq654 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq654
    | (have j0 := eq654 (σ X0) (σ X1)
       grind)
    | exact resolve eq654 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq15024 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1008 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq15025 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq15024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15024
  have eq15100 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15025 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15025
    | (have j0 := eq15025 (τ X0)
       grind)
    | exact resolve eq15025 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15025
  have eq15112 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15100 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15100
    | (have j0 := eq15100 X0
       grind)
    | exact resolve eq15100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15100
  have eq15119 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15112 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15112
    | (have j0 := eq15112 X0
       grind)
    | exact resolve eq15112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15112
  have eq15144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1007 x y
       grind)
    | exact superpose eq1007 eq16
    | (have j1 := eq1007 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1007 x y
       grind)
    | exact resolve eq16 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15151 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq1007 X0 X0
       grind)
    | exact superpose eq1007 eq68
    | (have j1 := eq1007 X0 X0
       grind)
    | exact resolve eq68 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1007
  have eq15323 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15151
  have eq15330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq15144
  have eq15349 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15119 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15119
    | (have j0 := eq15119 (τ X0)
       grind)
    | exact resolve eq15119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15361 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15349 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15349
    | (have j0 := eq15349 X0
       grind)
    | exact resolve eq15349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq15368 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15361 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15361
    | (have j0 := eq15361 X0
       grind)
    | exact resolve eq15361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15361
  have eq15374 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15368 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq15368
    | (have j0 := eq15368 (τ X0)
       grind)
    | exact resolve eq15368 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15368
  have eq15560 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15323 (τ X0)
       have i₂ := eq665 X0 (τ X0)
       grind)
    | exact superpose eq665 eq15323
    | (have j0 := eq15323 (τ X0)
       have j1 := eq665 X0 (τ X0)
       grind)
    | exact resolve eq15323 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq15323
  have eq15661 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq15560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560
  have eq15670 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15661 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15661
    | (have j0 := eq15661 X0
       grind)
    | exact resolve eq15661 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15661
  have eq15678 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15670 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15670
    | (have j0 := eq15670 X0
       grind)
    | exact resolve eq15670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670
  have eq15698 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k X1 (τ X0)) ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X0)
       have i₂ := eq15678 X0
       grind)
    | exact superpose eq15678 eq12
    | (have j1 := eq15678 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq15678 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq15678 X0
       grind)
    | exact resolve eq12 eq15678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15678
  have eq15824 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15698
  have eq15904 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15119 (τ X0)
       have i₂ := eq15824 X0 (τ X0)
       grind)
    | exact superpose eq15824 eq15119
    | (have j0 := eq15119 (τ X0)
       have j1 := eq15824 X0 x
       grind)
    | exact resolve eq15119 eq15824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15119 eq15824
  have eq15938 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15904
  have eq15958 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15938 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15938
    | (have j0 := eq15938 X0
       grind)
    | exact resolve eq15938 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15938
  have eq15959 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15958 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq15987 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15959 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq15959
    | (have j0 := eq15959 (σ X0)
       grind)
    | exact resolve eq15959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15959
  have eq43904 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90 (σ x) (σ y)
       have i₂ := eq15330
       grind)
    | exact superpose eq15330 eq90
    | exact resolve eq90 eq15330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq44023 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq43904
  have eq44091 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq44023
  have eq44202 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq44091
       grind)
    | exact superpose eq44091 eq12
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq44091
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq44091
       grind)
    | exact resolve eq12 eq44091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44091
  have eq44395 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq44202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44202
  have eq44515 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15374 (σ x)
       have i₂ := eq44395 (σ x)
       grind)
    | exact superpose eq44395 eq15374
    | (have j0 := eq15374 (σ x)
       grind)
    | exact resolve eq15374 eq44395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374 eq44395
  have eq44618 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq44515
  have eq44675 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44618
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44618
    | exact resolve eq44618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44618
  have eq44676 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq44675
  have eq44720 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq44676
  have eq44810 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90 x y
       have i₂ := eq44720
       grind)
    | exact superpose eq44720 eq90
    | exact resolve eq90 eq44720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44720
  have eq44929 : x = (M.op x x) := by grind
  clear eq44810
  have eq45103 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq44929
       grind)
    | exact superpose eq44929 eq12
    | (have r₁ := eq12 X0 x
       have r₂ := eq44929
       grind)
    | exact resolve eq12 eq44929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45108 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq44929
       grind)
    | exact superpose eq44929 eq76
    | exact resolve eq76 eq44929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq45202 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq443 x x x
       have i₂ := eq44929
       grind)
    | exact superpose eq44929 eq443
    | exact resolve eq443 eq44929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44929
  have eq45296 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq45103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45103
  have eq45323 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq45202 X0
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq45202
    | exact resolve eq45202 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq45202
  have eq46511 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15987 x
       have i₂ := eq45296 x
       grind)
    | exact superpose eq45296 eq15987
    | (have j0 := eq15987 x
       grind)
    | exact resolve eq15987 eq45296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15987 eq45296
  have eq46591 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq46511
  have eq48147 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45108 X0
       have i₂ := eq45323 X0
       grind)
    | exact superpose eq45323 eq45108
    | exact resolve eq45108 eq45323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45108 eq45323
  have eq48148 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48147 y
       grind)
    | exact superpose eq48147 eq16
    | exact resolve eq16 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48237 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 x X1 X0 X2
       have i₂ := eq48147 X0
       grind)
    | exact superpose eq48147 eq207
    | exact resolve eq207 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq48252 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 x X1 X0
       have i₂ := eq48147 X0
       grind)
    | exact superpose eq48147 eq443
    | exact resolve eq443 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq48725 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48252 X0 X0
       have i₂ := eq48147 X0
       grind)
    | exact superpose eq48147 eq48252
    | exact resolve eq48252 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48252
  have eq48739 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48237 X0 X0 X2
       have i₂ := eq48147 X0
       grind)
    | exact superpose eq48147 eq48237
    | exact resolve eq48237 eq48147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48147 eq48237
  have eq56119 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48739 (σ x) (σ x) X0
       have i₂ := eq46591
       grind)
    | exact superpose eq46591 eq48739
    | exact resolve eq48739 eq46591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46591 eq48739
  have eq56379 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56119 X0
       have i₂ := eq48725 X0 (σ x)
       grind)
    | exact superpose eq48725 eq56119
    | exact resolve eq56119 eq48725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48725 eq56119
  have eq56600 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq48148
       have i₂ := eq56379 (σ y)
       grind)
    | exact superpose eq56379 eq48148
    | (have r₁ := eq48148
       have r₂ := eq56379 (σ y)
       grind)
    | exact resolve eq48148 eq56379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48148 eq56379
  have eq56708 : False := by grind
  exact eq56708

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq19
    | exact resolve eq19 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X0 X0) X0 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq62
    | exact resolve eq62 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq77 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq727 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1851 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq727 X1 X0
       grind)
    | exact superpose eq727 eq15
    | (have j1 := eq727 X1 X0
       grind)
    | exact resolve eq15 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3337 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 x
       have i₂ := eq750 (τ x) x
       grind)
    | exact superpose eq750 eq65
    | (have j1 := eq750 (τ X0) X0
       grind)
    | exact resolve eq65 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq750
  have eq3344 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq3337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3346 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3344 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3344
    | (have j0 := eq3344 X0
       grind)
    | exact resolve eq3344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3402 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq3346 (τ X0)
       grind)
    | exact superpose eq3346 eq19
    | (have j1 := eq3346 (τ X0)
       grind)
    | exact resolve eq19 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3346
  have eq3408 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3402 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq3402
    | (have j0 := eq3402 X0
       grind)
    | exact resolve eq3402 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402
  have eq3427 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3408 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3408
    | (have j0 := eq3408 X0
       grind)
    | exact resolve eq3408 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq6740 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) X1) = X1 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (τ (τ X0)) X1
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq77
    | (have j1 := eq3427 X0
       grind)
    | exact resolve eq77 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6790 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) (M.op (τ (τ X0)) X1)) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq522 (τ (τ X0)) (τ (τ X0)) x
       have i₂ := eq3427 X0
       grind)
    | exact superpose eq3427 eq522
    | (have j1 := eq3427 X0
       grind)
    | exact resolve eq522 eq3427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq6812 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6790 X0 X1
       have i₂ := eq90 (τ (τ X0)) X1
       grind)
    | exact superpose eq90 eq6790
    | (have j0 := eq6790 X0 X1
       grind)
    | exact resolve eq6790 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790
  have eq13739 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq6812 eq6740
    | (have j0 := eq6740 X0 X1
       have j1 := eq6812 X0 X1
       grind)
    | exact resolve eq6740 eq6812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740
  have eq13909 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ X0)) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | exact superpose eq13739 eq6812
    | (have j0 := eq6812 X0 X1
       have j1 := eq13739 X0 X1
       grind)
    | exact resolve eq6812 eq13739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812 eq13739
  have eq15312 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq13909 (σ X0) X1
       grind)
    | exact superpose eq13909 eq23
    | (have j1 := eq13909 (σ X0) X1
       grind)
    | exact resolve eq23 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq15362 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15312 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq15312
    | (have j0 := eq15312 X0 X1
       grind)
    | exact resolve eq15312 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15312
  have eq15406 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (τ (σ X0))) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15362 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15362
    | (have j0 := eq15362 X0 X1
       grind)
    | exact resolve eq15362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15362
  have eq15442 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15406 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15406
    | (have j0 := eq15406 X0 X1
       grind)
    | exact resolve eq15406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15406
  have eq15520 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq15442 (σ X0) X1
       grind)
    | exact superpose eq15442 eq23
    | (have j1 := eq15442 (σ X0) X1
       grind)
    | exact resolve eq23 eq15442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15442
  have eq15570 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15520 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq15520
    | (have j0 := eq15520 X0 X1
       grind)
    | exact resolve eq15520 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15520
  have eq15614 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15570 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15570
    | (have j0 := eq15570 X0 X1
       grind)
    | exact resolve eq15570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570
  have eq15650 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15614 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15614
    | (have j0 := eq15614 X0 X1
       grind)
    | exact resolve eq15614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15614
  have eq15728 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq15650 (σ X0) X1
       grind)
    | exact superpose eq15650 eq23
    | (have j1 := eq15650 (σ X0) X1
       grind)
    | exact resolve eq23 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15778 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15728 X1 X1
       have i₂ := eq23 (σ X1) X1
       grind)
    | exact superpose eq23 eq15728
    | (have j0 := eq15728 X0 X1
       grind)
    | exact resolve eq15728 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15728
  have eq15821 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15778 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15778
    | (have j0 := eq15778 X0 X1
       grind)
    | exact resolve eq15778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15778
  have eq24204 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0)
       have i₂ := eq1851 X0 X0 X0
       grind)
    | exact superpose eq1851 eq64
    | (have j1 := eq1851 X0 (k (k X0 X0) X0) x
       grind)
    | exact resolve eq64 eq1851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1851
  have eq24221 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq24204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24204
  have eq24238 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq15821 eq24221
    | (have j0 := eq24221 X0
       have j1 := eq15821 X0 (σ X0)
       grind)
    | exact resolve eq24221 eq15821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15821 eq24221
  have eq24298 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq24238 (τ X0)
       grind)
    | exact superpose eq24238 eq18
    | (have j1 := eq24238 (τ X0)
       grind)
    | exact resolve eq18 eq24238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24238
  have eq24385 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq24298 X0
       have j1 := eq12 X0 (σ (τ X0))
       grind)
    | (have r₁ := eq24298 X0
       have r₂ := eq12 X0 (σ (τ X0))
       grind)
    | exact resolve eq24298 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24298
  have eq24405 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24385 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24385
    | exact resolve eq24385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24385
  have eq24497 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq24405 (σ X0)
       grind)
    | exact superpose eq24405 eq15
    | exact resolve eq15 eq24405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24511 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq24405 (τ X0)
       grind)
    | exact superpose eq24405 eq32
    | exact resolve eq32 eq24405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq24543 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24511 X0
       have i₂ := eq24405 X0
       grind)
    | exact superpose eq24405 eq24511
    | exact resolve eq24511 eq24405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24511
  have eq24557 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24497 X0
       have i₂ := eq24405 X0
       grind)
    | exact superpose eq24405 eq24497
    | exact resolve eq24497 eq24405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24405 eq24497
  have eq24691 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 (τ X0) X1
       have i₂ := eq24543 X0
       grind)
    | exact superpose eq24543 eq77
    | exact resolve eq77 eq24543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24543
  have eq24808 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq24557 X1
       grind)
    | exact superpose eq24557 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq24848 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq24557 X0
       grind)
    | exact superpose eq24557 eq9
    | exact resolve eq9 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24868 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0) (σ X0)
       have i₂ := eq24557 X0
       grind)
    | exact superpose eq24557 eq90
    | exact resolve eq90 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24939 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24808 X0 X1
       have i₂ := eq24557 X1
       grind)
    | exact superpose eq24557 eq24808
    | (have j0 := eq24808 X0 X1
       grind)
    | exact resolve eq24808 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24808
  have eq25827 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24848 (σ X0) X1
       have i₂ := eq24557 X0
       grind)
    | exact superpose eq24557 eq24848
    | exact resolve eq24848 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24557 eq24848
  have eq26202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24939 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq24939
    | (have j0 := eq24939 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq24939 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24939
  have eq37574 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26202 x y
       grind)
    | exact superpose eq26202 eq16
    | (have j1 := eq26202 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq26202 x y
       grind)
    | exact resolve eq16 eq26202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26202
  have eq37888 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq37574
  have eq59750 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq37888
       grind)
    | exact superpose eq37888 eq10
    | exact resolve eq10 eq37888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37888
  have eq59964 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59750
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq59750
    | exact resolve eq59750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59750
  have eq59965 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq59964
  have eq60033 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq59965
       grind)
    | exact superpose eq59965 eq10
    | exact resolve eq10 eq59965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59965
  have eq60248 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq60033
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq60033
    | exact resolve eq60033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60033
  have eq60249 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq60248
  have eq60411 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24868 x
       have i₂ := eq60249
       grind)
    | exact superpose eq60249 eq24868
    | exact resolve eq24868 eq60249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24868
  have eq60535 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90 x x
       have i₂ := eq60249
       grind)
    | exact superpose eq60249 eq90
    | exact resolve eq90 eq60249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60249
  have eq61902 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60411
       grind)
    | exact superpose eq60411 eq16
    | exact resolve eq16 eq60411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60411
  have eq62053 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq60535 eq61902
    | exact resolve eq61902 eq60535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60535 eq61902
  have eq62054 : x = (M.op x x) := by grind
  clear eq62053
  have eq62123 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 x X0
       have i₂ := eq62054
       grind)
    | exact superpose eq62054 eq77
    | exact resolve eq77 eq62054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq62163 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24691 x X0
       have i₂ := eq62054
       grind)
    | exact superpose eq62054 eq24691
    | exact resolve eq24691 eq62054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24691
  have eq62364 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq522 x x x
       have i₂ := eq62054
       grind)
    | exact superpose eq62054 eq522
    | exact resolve eq522 eq62054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62054
  have eq62410 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq62364 X0
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq62364
    | exact resolve eq62364 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq62364
  have eq63056 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62123 X0
       have i₂ := eq62410 X0
       grind)
    | exact superpose eq62410 eq62123
    | exact resolve eq62123 eq62410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62123 eq62410
  have eq63057 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63056 y
       grind)
    | exact superpose eq63056 eq16
    | exact resolve eq16 eq63056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63306 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 x X1 X0
       have i₂ := eq63056 X0
       grind)
    | exact superpose eq63056 eq522
    | exact resolve eq522 eq63056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq63574 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63306 X0 X0
       have i₂ := eq63056 X0
       grind)
    | exact superpose eq63056 eq63306
    | exact resolve eq63306 eq63056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63056 eq63306
  have eq66051 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62163 X0
       have i₂ := eq63574 X0 (τ x)
       grind)
    | exact superpose eq63574 eq62163
    | exact resolve eq62163 eq63574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62163
  have eq66149 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25827 (τ x) X0
       have i₂ := eq66051 (τ x)
       grind)
    | exact superpose eq66051 eq25827
    | exact resolve eq25827 eq66051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25827 eq66051
  have eq66381 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66149 X0
       have i₂ := eq63574 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq63574 eq66149
    | exact resolve eq66149 eq63574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63574 eq66149
  have eq66497 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66381 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq66381
    | exact resolve eq66381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66381
  have eq66637 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq63057
       have i₂ := eq66497 (σ y)
       grind)
    | exact superpose eq66497 eq63057
    | (have r₁ := eq63057
       have r₂ := eq66497 (σ y)
       grind)
    | exact resolve eq63057 eq66497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63057 eq66497
  have eq66889 : False := by grind
  exact eq66889

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23
    | exact resolve eq23 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq29
    | exact resolve eq29 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq65 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65
    | (have j0 := eq65 X0
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq67 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | (have j0 := eq64 X0
       grind)
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq72 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq72 (M.op X0 X1)
       grind)
    | exact superpose eq72 eq52
    | exact resolve eq52 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) X0 X2
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq52
    | exact resolve eq52 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq9
    | exact resolve eq9 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq9
    | (have j1 := eq80 X0 X1
       grind)
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 (σ X0)
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq72
    | (have j1 := eq80 X0 X0
       grind)
    | exact resolve eq72 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq312 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq317 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq536 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) (τ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0 X1
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq41
    | (have j1 := eq67 (σ X0)
       grind)
    | exact resolve eq41 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq537 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0 X1
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq33
    | (have j1 := eq67 (σ X0)
       grind)
    | exact resolve eq33 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq67
  have eq554 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq555 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k (M.op (τ (σ X0)) (τ (σ X0))) X0) (τ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq536
    | (have j0 := eq536 X0 X1
       grind)
    | exact resolve eq536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq562 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k (M.op X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq563 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (k (M.op X0 X0) X0) (τ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq569 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k (M.op X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq562
  have eq570 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k (M.op X0 X0) X0) (τ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq563
  have eq571 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq572 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (k (M.op X0 X0) X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq570
    | (have j0 := eq570 X0 X1
       grind)
    | exact resolve eq570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1501 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 x
       have i₂ := eq80 x x
       grind)
    | exact superpose eq80 eq66
    | (have j0 := eq66 X0
       have j1 := eq80 X0 X0
       grind)
    | exact resolve eq66 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1519 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1532 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1519 X0
       have j1 := eq313 X0
       grind)
    | (have r₁ := eq1519 X0
       have r₂ := eq313 X0
       grind)
    | exact resolve eq1519 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1541 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1532 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1532
    | (have j0 := eq1532 X0
       grind)
    | exact resolve eq1532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1731 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq1541 X0
       grind)
    | exact superpose eq1541 eq12
    | (have j1 := eq1541 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq1541 X0
       grind)
    | exact resolve eq12 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1739 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1731 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1760 : ∀ X0 X1 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) X0 (τ X0)
       have i₂ := eq1739 (τ X0) X1
       grind)
    | exact superpose eq1739 eq28
    | (have j1 := eq1739 (τ X0) (k (σ (τ X0)) X0)
       grind)
    | exact resolve eq28 eq1739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1739
  have eq1788 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1760 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1760
    | (have j0 := eq1760 X0 X1
       grind)
    | exact resolve eq1760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1803 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1788 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1788
    | (have j0 := eq1788 X0 X1
       grind)
    | exact resolve eq1788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1834 : ∀ X0 : G, X0 ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1803 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1835 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq1877 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq1835 X0
       grind)
    | exact superpose eq1835 eq14
    | (have j0 := eq14 X0 X0
       grind)
    | exact resolve eq14 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1899 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1877 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1877 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1877 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1951 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1951 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1951
    | (have j0 := eq1951 X0 X1
       grind)
    | exact resolve eq1951 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2098 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq317 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq317
    | exact resolve eq317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2144 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2098 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2098
    | (have j0 := eq2098 X0
       grind)
    | exact resolve eq2098 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2098
  have eq2154 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2144 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2144
    | (have j0 := eq2144 X0
       grind)
    | exact resolve eq2144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq2165 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2154 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq2154
    | (have j0 := eq2154 (τ X0)
       grind)
    | exact resolve eq2154 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2404 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k (M.op X1 X1) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq571
    | (have j0 := eq571 X1 X1
       grind)
    | exact resolve eq571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq2491 : ∀ X0 X1 : G, (k X1 X0) = (k (k (M.op X1 X1) X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq572
    | (have j0 := eq572 X1 X1
       grind)
    | exact resolve eq572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq5827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq294
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq294
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq5830 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq5827
  have eq5984 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq295 (τ X0) (τ X1) X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq295
    | (have j0 := eq295 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq295 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq6101 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5984 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5984
    | (have j0 := eq5984 X0 X1 X2
       grind)
    | exact resolve eq5984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984
  have eq6112 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6101 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6101
    | (have j0 := eq6101 X0 X1 X2
       grind)
    | exact resolve eq6101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101
  have eq6120 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6112 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6112
    | (have j0 := eq6112 X0 X1 X2
       grind)
    | exact resolve eq6112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6112
  have eq6124 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6120 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6120
    | (have j0 := eq6120 X0 X1 X2
       grind)
    | exact resolve eq6120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6120
  have eq6126 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6124 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6124
    | (have j0 := eq6124 X0 X1 X2
       grind)
    | exact resolve eq6124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124
  have eq6127 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6126 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6126
    | (have j0 := eq6126 X0 X1 X2
       grind)
    | exact resolve eq6126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6126
  have eq20940 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (k X1 X0) X1 X0
       have i₂ := eq6127 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6127 eq96
    | (have j1 := eq6127 X1 X0 x
       grind)
    | exact resolve eq96 eq6127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq6127
  have eq44204 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5830
       have i₂ := eq80 y y
       grind)
    | exact superpose eq80 eq5830
    | (have j1 := eq80 y y
       grind)
    | exact resolve eq5830 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq5830
  have eq44329 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq44204
  have eq44370 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have j1 := eq313 y
       grind)
    | (have r₁ := eq44329
       have r₂ := eq313 y
       grind)
    | exact resolve eq44329 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq44329
  have eq68574 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20940 X0 X0
       have i₂ := eq2154 X0
       grind)
    | exact superpose eq2154 eq20940
    | (have j0 := eq20940 X0 X0
       have j1 := eq2154 X0
       grind)
    | exact resolve eq20940 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq68575 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20940 X0 X0
       have i₂ := eq1899 X0
       grind)
    | exact superpose eq1899 eq20940
    | (have j0 := eq20940 X0 X0
       have j1 := eq1899 X0
       grind)
    | exact resolve eq20940 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq20940
  have eq68782 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68575
  have eq68783 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq68574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68574
  have eq68784 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68782 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq68782 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq68782 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68782
  have eq68812 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68783 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq68783
    | (have j0 := eq68783 (σ X0)
       grind)
    | exact resolve eq68783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68783
  have eq69993 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68784 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq68784
    | exact resolve eq68784 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq555162 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq44370
       grind)
    | exact superpose eq44370 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq44370
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq44370
       grind)
    | exact resolve eq12 eq44370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44370
  have eq555546 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq555162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555162
  have eq555859 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq2165 (σ y)
       have i₂ := eq555546 (σ y)
       grind)
    | exact superpose eq555546 eq2165
    | (have j0 := eq2165 (σ y)
       grind)
    | exact resolve eq2165 eq555546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165 eq555546
  have eq556491 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq555859
  have eq556633 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq556491
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq556491
    | exact resolve eq556491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556491
  have eq556634 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq556633
  have eq556808 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1979 y y
       have i₂ := eq556634
       grind)
    | exact superpose eq556634 eq1979
    | (have j0 := eq1979 y y
       grind)
    | exact resolve eq1979 eq556634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq556634
  have eq556944 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq556808
  have eq559888 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq556944
       grind)
    | exact superpose eq556944 eq10
    | exact resolve eq10 eq556944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556944
  have eq560086 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq559888
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq559888
    | exact resolve eq559888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559888
  have eq560087 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq560086
  have eq560088 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq560087
       grind)
    | exact superpose eq560087 eq12
    | (have r₁ := eq12 X0 y
       have r₂ := eq560087
       grind)
    | exact resolve eq12 eq560087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560092 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq78 y X0
       have i₂ := eq560087
       grind)
    | exact superpose eq560087 eq78
    | exact resolve eq78 eq560087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560206 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq702 y y x
       have i₂ := eq560087
       grind)
    | exact superpose eq560087 eq702
    | exact resolve eq702 eq560087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560087
  have eq560475 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq560088 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560088
  have eq560579 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq560206 X0
       have i₂ := eq99 y X0
       grind)
    | exact superpose eq99 eq560206
    | exact resolve eq560206 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560206
  have eq562421 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68812 y
       have i₂ := eq560475 y
       grind)
    | exact superpose eq560475 eq68812
    | (have j0 := eq68812 y
       grind)
    | exact resolve eq68812 eq560475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68812 eq560475
  have eq562935 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq562421
  have eq569368 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq78 (σ y) X0
       have i₂ := eq562935
       grind)
    | exact superpose eq562935 eq78
    | exact resolve eq78 eq562935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq569482 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq702 (σ y) (σ y) x
       have i₂ := eq562935
       grind)
    | exact superpose eq562935 eq702
    | exact resolve eq702 eq562935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq562935
  have eq569866 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq569482 X0
       have i₂ := eq99 (σ y) X0
       grind)
    | exact superpose eq99 eq569482
    | exact resolve eq569482 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569482
  have eq573218 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq560092 X0
       have i₂ := eq560579 X0
       grind)
    | exact superpose eq560579 eq560092
    | exact resolve eq560092 eq560579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560092
  have eq573818 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq573218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573218
  have eq574118 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 y y
       have i₂ := eq573818 X0
       grind)
    | exact superpose eq573818 eq99
    | (have j1 := eq573818 x
       grind)
    | exact resolve eq99 eq573818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573818
  have eq575325 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq574118 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574118
  have eq575326 : x = (M.op y x) := by grind
  clear eq575325
  have eq575328 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq560579 x
       have i₂ := eq575326
       grind)
    | exact superpose eq575326 eq560579
    | exact resolve eq560579 eq575326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560579
  have eq575330 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq575326
       grind)
    | exact superpose eq575326 eq9
    | exact resolve eq9 eq575326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575326
  have eq662638 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq569368 X0
       have i₂ := eq569866 X0
       grind)
    | exact superpose eq569866 eq569368
    | exact resolve eq569368 eq569866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569368
  have eq663291 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq662638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662638
  have eq663331 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq569866 X0
       have i₂ := eq663291 X0
       grind)
    | exact superpose eq663291 eq569866
    | exact resolve eq569866 eq663291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569866 eq663291
  have eq664413 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq663331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663331
  have eq666563 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq664413 (σ x)
       grind)
    | exact superpose eq664413 eq16
    | exact resolve eq16 eq664413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664413
  have eq666721 : (σ y) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq666563
       have i₂ := eq575328
       grind)
    | exact superpose eq575328 eq666563
    | exact resolve eq666563 eq575328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575328 eq666563
  have eq666724 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq666721
  have eq666725 : x = (M.op y y) := by grind
  clear eq666724
  have eq666750 : ∀ X0 : G, x ≠ y ∨ x = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq12
    | exact resolve eq12 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666751 : y = (k x y) ∨ x = y := by grind
  have eq666752 : y = (M.op x y) := by
    first
    | (have i₁ := eq72 y
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq72
    | exact resolve eq72 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq666784 : ∀ X0 : G, (k X0 y) = (k X0 (k x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2404 X0 y
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq2404
    | exact resolve eq2404 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2404
  have eq666789 : ∀ X0 : G, (k y X0) = (k (k x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2491 X0 y
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq2491
    | exact resolve eq2491 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq666999 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq9
    | exact resolve eq9 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676957 : (k y (k x y)) = (k (k x y) y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq666784 (k x y)
       have i₂ := eq666789 (k x y)
       grind)
    | exact superpose eq666789 eq666784
    | exact resolve eq666784 eq666789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666784 eq666789
  have eq676976 : (k y (k x y)) = (k (k x y) y) ∨ x = y := by grind
  clear eq676957
  have eq720184 : (k y (k x y)) = (M.op (k x y) y) ∨ (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 (k x y) y
       have i₂ := eq676976
       grind)
    | exact superpose eq676976 eq14
    | (have j0 := eq14 (k x y) y
       grind)
    | exact resolve eq14 eq676976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676976
  have eq720254 : (k y (k x y)) = (M.op (k x y) y) ∨ (k x y) = (M.op y y) ∨ x = y := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq720184
       have r₂ := eq12 x y
       grind)
    | exact resolve eq720184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720184
  have eq720281 : x = (k x y) ∨ (k y (k x y)) = (M.op (k x y) y) ∨ x = y := by
    first
    | (have i₁ := eq720254
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq720254
    | exact resolve eq720254 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720254
  have eq720308 : (k y (k x y)) = (M.op (k x y) y) ∨ x = (k x y) := by
    first
    | (have j1 := eq666750 x
       grind)
    | (have r₁ := eq720281
       have r₂ := eq666750 x
       grind)
    | exact resolve eq720281 eq666750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720281
  have eq920664 : (M.op y y) = (k y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq720308
       have i₂ := eq666751
       grind)
    | exact superpose eq666751 eq720308
    | exact resolve eq720308 eq666751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666751 eq720308
  have eq920733 : (M.op y y) = (k y y) ∨ x = y := by grind
  clear eq920664
  have eq920749 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq920733
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq920733
    | exact resolve eq920733 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920733
  have eq920751 : x = (k y y) := by
    first
    | (have j1 := eq666750 y
       grind)
    | (have r₁ := eq920749
       have r₂ := eq666750 x
       grind)
    | exact resolve eq920749 eq666750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666750 eq920749
  have eq920823 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq317 y
       have i₂ := eq920751
       grind)
    | exact superpose eq920751 eq317
    | (have j0 := eq317 y
       grind)
    | exact resolve eq317 eq920751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq920751
  have eq936677 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq920823
       grind)
    | exact superpose eq920823 eq12
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq920823
       grind)
    | exact resolve eq12 eq920823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920823
  have eq937262 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq936677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936677
  have eq937592 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq937262 X0
       grind)
    | exact superpose eq937262 eq16
    | (have j1 := eq937262 X0
       grind)
    | exact resolve eq16 eq937262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937262
  have eq938294 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq937592 X0
       have i₂ := eq666752
       grind)
    | exact superpose eq666752 eq937592
    | (have j0 := eq937592 X0
       grind)
    | exact resolve eq937592 eq666752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666752 eq937592
  have eq938295 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq938294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938294
  have eq938543 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq68784 (σ y)
       have i₂ := eq938295 (σ y)
       grind)
    | exact superpose eq938295 eq68784
    | exact resolve eq68784 eq938295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68784
  have eq938568 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq69993 (σ y)
       have i₂ := eq938295 (σ y)
       grind)
    | exact superpose eq938295 eq69993
    | exact resolve eq69993 eq938295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69993 eq938295
  have eq939099 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by grind
  clear eq938568
  have eq939103 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq938543
  have eq939320 : y = (M.op y y) := by
    first
    | (have i₁ := eq939099
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq939099
    | exact resolve eq939099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939099
  have eq939512 : x = y := by
    first
    | (have i₁ := eq939320
       have i₂ := eq666725
       grind)
    | exact superpose eq666725 eq939320
    | exact resolve eq939320 eq666725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666725 eq939320
  have eq939596 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq939512
       grind)
    | exact superpose eq939512 eq16
    | exact resolve eq16 eq939512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq939644 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq575330 X0
       have i₂ := eq939512
       grind)
    | exact superpose eq939512 eq575330
    | exact resolve eq575330 eq939512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575330
  have eq939714 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq666999 X0
       have i₂ := eq939512
       grind)
    | exact superpose eq939512 eq666999
    | exact resolve eq666999 eq939512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666999
  have eq939762 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq939714 X0
       have i₂ := eq99 x X0
       grind)
    | exact superpose eq99 eq939714
    | exact resolve eq939714 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq939714
  have eq966457 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq939103
       have i₂ := eq939512
       grind)
    | exact superpose eq939512 eq939103
    | exact resolve eq939103 eq939512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939103 eq939512
  have eq1000504 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq939644 X0
       have i₂ := eq939762 X0
       grind)
    | exact superpose eq939762 eq939644
    | exact resolve eq939644 eq939762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939644
  have eq1000516 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq939762 X0
       have i₂ := eq1000504 X0
       grind)
    | exact superpose eq1000504 eq939762
    | exact resolve eq939762 eq1000504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939762 eq1000504
  have eq1072808 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq939596
       have i₂ := eq1000516 x
       grind)
    | exact superpose eq1000516 eq939596
    | exact resolve eq939596 eq1000516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939596 eq1000516
  have eq1072809 : False := by grind
  exact eq1072809

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq183 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq209 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq212 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq209 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq209
    | exact resolve eq209 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1971 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190 x y
       grind)
    | exact superpose eq190 eq16
    | (have j1 := eq190 x y
       grind)
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq14520 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq14622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14520 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14520
    | (have j0 := eq14520 X0 X1
       grind)
    | exact resolve eq14520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520
  have eq19941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1971
       have i₂ := eq14622 x y
       grind)
    | exact superpose eq14622 eq1971
    | (have j1 := eq14622 x y
       grind)
    | (have r₁ := eq1971
       have r₂ := eq14622 x y
       grind)
    | (have r₁ := eq1971
       have r₂ := eq14622 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1971
       have r₂ := eq14622 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1971 eq14622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971 eq14622
  have eq19942 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq19941
  have eq22892 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19942
       grind)
    | exact superpose eq19942 eq16
    | exact resolve eq16 eq19942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19942
  have eq22893 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq22892
       have r₂ := eq23 x
       grind)
    | exact resolve eq22892 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22892
  have eq22895 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22893
       grind)
    | exact superpose eq22893 eq10
    | exact resolve eq10 eq22893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22893
  have eq22982 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22895
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22895
    | exact resolve eq22895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22895
  have eq22984 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22982
       grind)
    | exact superpose eq22982 eq16
    | exact resolve eq16 eq22982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22982
  have eq22985 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22984
       have r₂ := eq23 x
       grind)
    | exact resolve eq22984 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22984
  have eq23023 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq22985
       grind)
    | exact superpose eq22985 eq10
    | exact resolve eq10 eq22985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22985
  have eq23110 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23023
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23023
    | exact resolve eq23023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23023
  have eq23111 : x = (M.op y y) := by grind
  clear eq23110
  have eq23135 : y = (M.op x y) := by
    first
    | (have i₁ := eq209 y
       have i₂ := eq23111
       grind)
    | exact superpose eq23111 eq209
    | exact resolve eq209 eq23111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq23136 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 y
       have i₂ := eq23111
       grind)
    | exact superpose eq23111 eq212
    | exact resolve eq212 eq23111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq23111
  have eq23590 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23136
       grind)
    | exact superpose eq23136 eq16
    | exact resolve eq16 eq23136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23136
  have eq23669 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq23590
       have i₂ := eq23135
       grind)
    | exact superpose eq23135 eq23590
    | exact resolve eq23590 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135 eq23590
  have eq23670 : False := by grind
  exact eq23670

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) X2) (σ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (σ X0) (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq617 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (σ (M.op X1 X1)) (M.op (σ X1) X2)) X0) (σ X1)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op (M.op (σ (M.op X1 X1)) (M.op (σ X1) X2)) X0) (σ X1)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 (M.op (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) X2) (σ X0)) X2 X2
       have i₂ := eq67 X0 X1 X2
       grind)
    | exact superpose eq67 eq73
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq647 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq617 x X0 x X3
       have i₂ := eq67 X0 x x
       grind)
    | exact superpose eq67 eq617
    | exact resolve eq617 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq617
  have eq1945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq79 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq79 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq79 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1994 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1945
  have eq2179 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq647 (σ x) (σ y)
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq647
    | exact resolve eq647 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2183 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2179
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq2179
    | exact resolve eq2179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq4918 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2183
       grind)
    | exact superpose eq2183 eq10
    | exact resolve eq10 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq4957 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq4918
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4918
    | exact resolve eq4918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq7169 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq4957
       grind)
    | exact superpose eq4957 eq647
    | exact resolve eq647 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq7173 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7169
  have eq9896 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq7173
       grind)
    | exact superpose eq7173 eq9
    | exact resolve eq9 eq7173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9897 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq7173
       grind)
    | exact superpose eq7173 eq9
    | exact resolve eq9 eq7173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173
  have eq9957 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9896 X0
       have i₂ := eq647 x X0
       grind)
    | (have i₁ := eq9896 X0
       have i₂ := eq647 x (M.op x X0)
       grind)
    | exact superpose eq647 eq9896
    | exact resolve eq9896 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq9896
  have eq22145 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9897 X0
       have i₂ := eq9957 X0
       grind)
    | exact superpose eq9957 eq9897
    | exact resolve eq9897 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897 eq9957
  have eq22286 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22145
  have eq25308 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq22286 X0
       grind)
    | exact superpose eq22286 eq10
    | (have j1 := eq22286 X0
       grind)
    | exact resolve eq10 eq22286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22286
  have eq25661 : ∀ X0 : G, x = y ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25308 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25308
    | (have j0 := eq25308 X0
       grind)
    | exact resolve eq25308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25308
  have eq25662 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq25661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25661
  have eq32075 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq25662 x
       grind)
    | exact superpose eq25662 eq52
    | exact resolve eq52 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq32145 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq25662 X0
       grind)
    | exact superpose eq25662 eq9
    | exact resolve eq9 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84412 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq32145 X1 X0
       have i₂ := eq25662 X0
       grind)
    | exact superpose eq25662 eq32145
    | exact resolve eq32145 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32145
  have eq85107 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq84412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84412
  have eq93003 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq85107 X0 X1
       grind)
    | exact superpose eq85107 eq16
    | (have j1 := eq85107 X1 X0
       grind)
    | exact resolve eq16 eq85107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85107
  have eq93033 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq93003 X0 X1
       grind)
    | (have r₁ := eq93003 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq93003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93003
  have eq202270 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32075 X0
       have i₂ := eq93033 (σ x) X0
       grind)
    | exact superpose eq93033 eq32075
    | exact resolve eq32075 eq93033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32075 eq93033
  have eq214980 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq202270 (σ y)
       grind)
    | exact superpose eq202270 eq16
    | exact resolve eq16 eq202270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202270
  have eq230862 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq214980
       have i₂ := eq25662 y
       grind)
    | exact superpose eq25662 eq214980
    | exact resolve eq214980 eq25662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25662 eq214980
  have eq230866 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq230862
  have eq230867 : x = y := by grind
  clear eq230866
  have eq238806 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230867
       grind)
    | exact superpose eq230867 eq16
    | exact resolve eq16 eq230867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230867
  have eq238807 : False := by grind
  exact eq238807

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq214 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq329 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq329 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq329 X0 X1
       grind)
    | exact superpose eq329 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq329 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq329 X1 X1
       grind)
    | exact resolve eq12 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq440 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq450 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq461 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X1 (M.op X1 X1) X2
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq553 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq214
  have eq566 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq342 (σ X0) (σ X0)
       grind)
    | exact superpose eq342 eq553
    | exact resolve eq553 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq574 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq566 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq566
    | exact resolve eq566 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq823 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X1
       have i₂ := eq329 X0 (σ X1)
       grind)
    | (have i₁ := eq574 X1
       have i₂ := eq329 (σ X1) X0
       grind)
    | exact superpose eq329 eq574
    | exact resolve eq574 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq4317 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq823 X1 (τ (M.op X1 X1))
       have i₂ := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq372 eq823
    | (have j1 := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq823 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq823
  have eq4361 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317
  have eq4492 : ∀ X0 X2 : G, (M.op (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq342 x X2
       have i₂ := eq4361 x X0
       grind)
    | exact superpose eq4361 eq342
    | exact resolve eq342 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4523 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq4361 X0 X1
       grind)
    | exact superpose eq4361 eq15
    | exact resolve eq15 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq4717 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq342 x X2
       have i₂ := eq4523 X0 x
       grind)
    | exact superpose eq4523 eq342
    | exact resolve eq342 eq4523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq5291 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq440 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq449 X1 X0 x
       grind)
    | exact superpose eq449 eq440
    | exact resolve eq440 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq5297 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5291 x X1 x
       have i₂ := eq461 x sF0 x
       grind)
    | exact superpose eq461 eq5291
    | exact resolve eq5291 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5333 : ∀ X1 : G, x = (M.op (M.op y (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq461 X1 x x
       have i₂ := eq5297 x
       grind)
    | exact superpose eq5297 eq461
    | exact resolve eq461 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297
  have eq5447 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq450 eq440
    | exact resolve eq440 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq5453 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5447 x X1 x
       have i₂ := eq461 x sF4 x
       grind)
    | exact superpose eq461 eq5447
    | exact resolve eq5447 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq5489 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq5453 eq461
    | exact resolve eq461 eq5453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq6890 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 (M.op X0 X1) X1 x X2 x
       have i₂ := eq53 X1 X0 x x
       grind)
    | exact superpose eq53 eq447
    | exact resolve eq447 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7007 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq440 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq447 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq440 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq447 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq447 eq440
    | exact resolve eq440 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq447
  have eq7143 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7007 X0 X1 x X3 x
       have i₂ := eq461 x (M.op X0 X1) x
       grind)
    | exact superpose eq461 eq7007
    | exact resolve eq7007 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq7007
  have eq19281 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op X1 (M.op X0 X1)) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7143 (M.op X1 (M.op X0 X1)) X3 x
       have i₂ := eq6890 X0 X1 x
       grind)
    | exact superpose eq6890 eq7143
    | exact resolve eq7143 eq6890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq19285 : ∀ X1 : G, x = (M.op X1 (M.op (M.op y (M.op x y)) X1)) := by
    intro X1
    first
    | exact superpose eq5333 eq7143
    | exact resolve eq7143 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19286 : ∀ X1 : G, (σ x) = (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X1
    first
    | exact superpose eq5489 eq7143
    | exact resolve eq7143 eq5489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5489 eq7143
  have eq21004 : (σ x) = (M.op (M.op (M.op y (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq19285 eq19286
    | exact resolve eq19286 eq19285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq41857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq41856
    | exact resolve eq41856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41856
  have eq41862 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq41857
       have r₂ := eq28
       grind)
    | exact resolve eq41857 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41857
  have eq41864 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq41862
    | exact resolve eq41862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41862
  have eq42000 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq41864 eq19281
    | exact resolve eq19281 eq41864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41864
  have eq42004 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19286 eq42000
    | exact resolve eq42000 eq19286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19286 eq42000
  have eq42030 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq42004 eq342
    | exact resolve eq342 eq42004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42004
  have eq44299 : ∀ X0 X1 : G, y = (M.op X0 (M.op (M.op y (M.op x y)) X0)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) X1) = X1 ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq19281 y y X0
       have i₂ := eq42030 X1
       grind)
    | (have i₁ := eq19281 X0 X1 x
       have i₂ := eq42030 (M.op X0 X1)
       grind)
    | exact superpose eq42030 eq19281
    | (have j1 := eq42030 X1
       grind)
    | exact resolve eq19281 eq42030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19281 eq42030
  have eq44304 : ∀ X1 : G, x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) X1) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq19285 eq44299
    | (have j0 := eq44299 x X1
       grind)
    | exact resolve eq44299 eq19285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285 eq44299
  have eq44366 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq342 y X0
       have i₂ := eq44304 X1
       grind)
    | exact superpose eq44304 eq342
    | (have j1 := eq44304 X1
       grind)
    | exact resolve eq342 eq44304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq44304
  have eq45405 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq44366
    | (have j0 := eq44366 X0 (σ y)
       grind)
    | exact resolve eq44366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44366
  have eq45786 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4717 x X0
       have i₂ := eq45405 x
       grind)
    | exact superpose eq45405 eq4717
    | exact resolve eq4717 eq45405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45405
  have eq45952 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq45786 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45786
    | (have j0 := eq45786 X0
       grind)
    | exact resolve eq45786 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45786
  have eq47459 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq45952 eq27
    | (have j1 := eq45952 (σ y)
       grind)
    | exact resolve eq27 eq45952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45952
  have eq47639 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47459
  have eq47715 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47639 eq28
    | exact resolve eq28 eq47639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47738 : (σ x) = (M.op (M.op (M.op y (M.op x y)) (M.op (σ y) (σ y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47639 eq21004
    | exact resolve eq21004 eq47639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21004 eq47639
  have eq47753 : (σ x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5333 eq47738
    | exact resolve eq47738 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333 eq47738
  have eq47821 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4492 x X0
       have i₂ := eq47753
       grind)
    | exact superpose eq47753 eq4492
    | exact resolve eq4492 eq47753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492 eq47753
  have eq47948 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29 eq47821
    | exact resolve eq47821 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47821
  have eq49543 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq47948 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47948
    | (have j0 := eq47948 y
       grind)
    | exact resolve eq47948 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47948
  have eq49841 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq49543 eq30
    | exact resolve eq30 eq49543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq49543
  have eq49910 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq49841
    | exact resolve eq49841 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49841
  have eq49911 : y = (M.op x y) ∨ x = y := by grind
  clear eq49910
  have eq49914 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq49911 eq21
    | exact resolve eq21 eq49911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50081 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49914
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq49914
    | exact resolve eq49914 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49914
  have eq50132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50081 eq47715
    | (have r₁ := eq47715
       have r₂ := eq50081
       grind)
    | exact resolve eq47715 eq50081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47715 eq50081
  have eq50135 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq50132
  have eq50136 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq50135
  have eq50164 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq50136 eq29
    | exact resolve eq29 eq50136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50136
  have eq50252 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq50164
    | exact resolve eq50164 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq50164
  have eq50348 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50252 eq49911
    | exact resolve eq49911 eq50252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49911 eq50252
  have eq50349 : x = y := by grind
  clear eq50348
  have eq50425 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq50349
       grind)
    | exact superpose eq50349 eq19
    | exact resolve eq19 eq50349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq50426 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq50349
       grind)
    | exact superpose eq50349 eq25
    | exact resolve eq25 eq50349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq50349
  have eq50571 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq50426
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50426
    | exact resolve eq50426 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq50426
  have eq50629 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50571 eq27
    | exact resolve eq27 eq50571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq50571
  have eq50721 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50425
       have i₂ := eq329 X0 x
       grind)
    | (have i₁ := eq50425
       have i₂ := eq329 x X0
       grind)
    | exact superpose eq329 eq50425
    | exact resolve eq50425 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq50425
  have eq51265 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50629 eq50721
    | exact resolve eq50721 eq50629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50629
  have eq51512 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4717 X0 (σ (M.op X0 X0))
       have i₂ := eq50721 (σ (M.op X0 X0))
       grind)
    | exact superpose eq50721 eq4717
    | exact resolve eq4717 eq50721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4717
  have eq51564 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq51512 x
       have i₂ := eq50721 x
       grind)
    | exact superpose eq50721 eq51512
    | exact resolve eq51512 eq50721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50721 eq51512
  have eq51781 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq51564
    | exact resolve eq51564 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51564
  have eq51908 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq51265 eq28
    | exact resolve eq28 eq51265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq51265
  have eq52005 : False := by grind
  exact eq52005

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_x_pxy_pyy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq77 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq155 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 x x X1
       have i₂ := eq54 x x X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq54 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X2
       have i₂ := eq54 X0 X1 X2
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq54 X0 X1 X3
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq261 : ∀ X0 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 X0) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq248 X0 x X2 X3
       have i₂ := eq254 x X0
       grind)
    | exact superpose eq254 eq248
    | (have j0 := eq248 X0 x X2 X3
       grind)
    | (have r₁ := eq248 (M.op x x) x (M.op x x) X3
       have r₂ := eq254 x (M.op (M.op x x) (M.op x x))
       grind)
    | exact resolve eq248 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq262 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op X3 X3) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq247 X0 X1 X2 X3
       have i₂ := eq254 X1 X0
       grind)
    | exact superpose eq254 eq247
    | (have j0 := eq247 X0 X1 X2 X3
       grind)
    | (have r₁ := eq247 (M.op X1 X1) X1 X2 (M.op X1 X1)
       have r₂ := eq254 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq247 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq263 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq246 X0 x X2 X3
       have i₂ := eq254 x X0
       grind)
    | exact superpose eq254 eq246
    | (have j0 := eq246 X0 x X2 X3
       grind)
    | (have r₁ := eq246 (M.op X0 X0) x (M.op (M.op x x) (M.op X0 X0)) X3
       have r₂ := eq254 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq246 X0 x (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0))) X3
       have r₂ := eq254 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq246 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq271 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ (M.op X2 X2) = X2 := by
    intro X2 X3
    first
    | (have j0 := eq261 x X2 X3
       grind)
    | (have r₁ := eq261 x x X3
       have r₂ := eq244 x x
       grind)
    | (have r₁ := eq261 x x X3
       have r₂ := eq244 x x
       grind)
    | exact resolve eq261 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq272 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq262 X0 X1 X2 X3
       grind)
    | (have r₁ := eq262 X1 X1 X2 X0
       have r₂ := eq244 X0 X1
       grind)
    | (have r₁ := eq262 X0 X1 X2 X1
       have r₂ := eq244 X0 X1
       grind)
    | exact resolve eq262 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq277 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq272 X0 x X2 X3
       have i₂ := eq254 x X0
       grind)
    | exact superpose eq254 eq272
    | (have j0 := eq272 X0 x X2 X3
       grind)
    | exact resolve eq272 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq307 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq254 X0 (M.op X0 X0)
       grind)
    | exact superpose eq254 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq254 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq254 X1 X0
       grind)
    | exact superpose eq254 eq9
    | exact resolve eq9 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq320 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X1) X0
       have i₂ := eq314 X1 (σ X0)
       grind)
    | exact superpose eq314 eq48
    | exact resolve eq48 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (M.op X1 X1)
       have i₂ := eq314 X1 (τ X0)
       grind)
    | exact superpose eq314 eq49
    | exact resolve eq49 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq324 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq321
    | exact resolve eq321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq392 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ (M.op X1 X1)))
       have i₂ := eq320 X0 X1
       grind)
    | exact superpose eq320 eq10
    | exact resolve eq10 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq410 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq392
    | exact resolve eq392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq422 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ (M.op X1 X1)) X0
       have i₂ := eq410 (σ X0) X1
       grind)
    | exact superpose eq410 eq48
    | exact resolve eq48 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq313 (M.op X0 (M.op X1 X1)) X3 x
       have i₂ := eq313 X0 x X1
       grind)
    | exact superpose eq313 eq313
    | exact resolve eq313 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ (τ (M.op X1 X1))))
       have i₂ := eq422 X0 X1
       grind)
    | exact superpose eq422 eq10
    | exact resolve eq10 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq653 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq635
    | exact resolve eq635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq674 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq324 (σ (M.op X0 X0)) X0
       have i₂ := eq155 (σ (M.op X0 X0))
       grind)
    | exact superpose eq155 eq324
    | (have j1 := eq155 (σ (M.op X0 X0))
       grind)
    | exact resolve eq324 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq677 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq410 (τ (M.op X0 X0)) X0
       have i₂ := eq155 (τ (M.op X0 X0))
       grind)
    | exact superpose eq155 eq410
    | (have j1 := eq155 (τ (M.op X0 X0))
       grind)
    | exact resolve eq410 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq155 sF3
       grind)
    | exact superpose eq155 eq68
    | (have j1 := eq155 (σ y)
       grind)
    | exact resolve eq68 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq681 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq684 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq703 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq53 X1 X0 X2 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq740 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (M.op X4 X4)) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X3 X3)) (M.op X1 (M.op X2 X2)) X4
       have i₂ := eq53 X1 X0 X3 X2
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq746 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq712 X0 X1 x x X4 X5
       have i₂ := eq313 (M.op X0 X1) x x
       grind)
    | exact superpose eq313 eq712
    | exact resolve eq712 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq772 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) ∨ (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq155 (τ (τ (M.op X0 X0)))
       have i₂ := eq653 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq653 eq155
    | (have j0 := eq155 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq155 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq653
  have eq777 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq772 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq844 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq271 X1 (σ X0)
       grind)
    | exact superpose eq271 eq48
    | (have j1 := eq271 X1 x
       grind)
    | exact resolve eq48 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq271 X1 (τ X0)
       grind)
    | exact superpose eq271 eq49
    | (have j1 := eq271 X1 x
       grind)
    | exact resolve eq49 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq271 X1 X0
       grind)
    | exact superpose eq271 eq128
    | (have j1 := eq271 X1 x
       grind)
    | exact resolve eq128 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq271 (σ X1) (σ X0)
       grind)
    | exact superpose eq271 eq15
    | (have j1 := eq271 (σ X1) x
       grind)
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq271 sF2 (σ X0)
       grind)
    | exact superpose eq271 eq31
    | (have j1 := eq271 (σ x) x
       grind)
    | exact resolve eq31 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq865 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35
       have i₂ := eq271 sF2 sF1
       grind)
    | exact superpose eq271 eq35
    | (have j1 := eq271 (σ x) x
       grind)
    | exact resolve eq35 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq870 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq42
       have i₂ := eq271 sF3 sF2
       grind)
    | exact superpose eq271 eq42
    | (have j1 := eq271 (σ y) x
       grind)
    | exact resolve eq42 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq874 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq870
    | exact resolve eq870 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq874
       have i₂ := eq271 y x
       grind)
    | exact superpose eq271 eq874
    | (have j1 := eq271 (σ y) x
       grind)
    | exact resolve eq874 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq874
  have eq887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq876
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq876
    | exact resolve eq876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq887
    | exact resolve eq887 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq889 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq888
       have r₂ := eq27
       grind)
    | exact resolve eq888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq909 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq889 eq410
    | exact resolve eq410 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq889
  have eq918 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39 eq909
    | exact resolve eq909 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq920 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq918 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq918 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq918 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq937 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq680
       have i₂ := eq920 y
       grind)
    | exact superpose eq920 eq680
    | exact resolve eq680 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq920
  have eq945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq937
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq937
    | exact resolve eq937 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq937
  have eq946 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq945
  have eq977 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq946 eq9
    | exact resolve eq9 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq946 eq244
    | exact resolve eq244 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq986 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq946 eq254
    | exact resolve eq254 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq987 : ∀ X0 X1 : G, (σ y) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq946 eq263
    | (have j0 := eq263 X0 X0 X1
       grind)
    | (have r₁ := eq263 (σ y) (σ y) x
       have r₂ := eq946
       grind)
    | exact resolve eq263 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq989 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq946 eq313
    | exact resolve eq313 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq997 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq946 eq461
    | exact resolve eq461 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq946
  have eq1007 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (σ y))) (M.op X3 X3))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq703 X0 x X2 X3
       have i₂ := eq997 X0 x
       grind)
    | exact superpose eq997 eq703
    | exact resolve eq703 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq1008 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (M.op X4 X4)) (M.op X1 (σ y))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq740 X0 X1 x X3 X4
       have i₂ := eq997 X1 x
       grind)
    | exact superpose eq997 eq740
    | exact resolve eq740 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq1009 : ∀ X0 X1 X5 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) = (M.op X1 (σ y)) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq746 X0 X1 x X5
       have i₂ := eq997 X1 x
       grind)
    | exact superpose eq997 eq746
    | exact resolve eq746 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1015 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (σ y)) (M.op y (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq713 x X1 X2
       have i₂ := eq997 x x
       grind)
    | exact superpose eq997 eq713
    | exact resolve eq713 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq1021 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0 x
       have i₂ := eq997 sF3 x
       grind)
    | exact superpose eq997 eq77
    | exact resolve eq77 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1025 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq989 X0 x
       have i₂ := eq997 X0 x
       grind)
    | exact superpose eq997 eq989
    | exact resolve eq989 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq997
  have eq1042 : ∀ X2 X3 : G, (σ y) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq277 x X2 X3
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq277
    | (have j0 := eq277 x X2 X3
       grind)
    | exact resolve eq277 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq1051 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq681 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq681
    | exact resolve eq681 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1054 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) := by
    first
    | (have i₁ := eq684 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq684
    | exact resolve eq684 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1057 : (τ (τ (σ y))) = (M.op (τ (τ (σ y))) (τ (τ (σ y)))) := by
    first
    | (have i₁ := eq777 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq777
    | exact resolve eq777 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1060 : ∀ X0 X1 : G, (σ y) = X1 ∨ (σ (k X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq985 X1
       grind)
    | exact superpose eq985 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq1061 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq985 X1
       grind)
    | exact superpose eq985 eq845
    | (have j0 := eq845 X0 X1
       grind)
    | exact resolve eq845 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1062 : ∀ X0 X1 : G, (σ y) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq985 X1
       grind)
    | exact superpose eq985 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1069 : ∀ X0 X1 : G, (σ X1) = (σ y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 X1
       have i₂ := eq985 (σ X1)
       grind)
    | exact superpose eq985 eq853
    | (have j0 := eq853 X0 X1
       grind)
    | exact resolve eq853 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1087 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq864 X0
       have i₂ := eq985 sF2
       grind)
    | exact superpose eq985 eq864
    | (have j0 := eq864 X0
       grind)
    | exact resolve eq864 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq1088 : (σ x) = (σ y) ∨ (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq865
       have i₂ := eq985 sF2
       grind)
    | exact superpose eq985 eq865
    | exact resolve eq865 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq1093 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq1021 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1021
    | exact resolve eq1021 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1098 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (σ y)) (M.op y (σ y))) := by
    intro X1
    first
    | (have i₁ := eq1015 X1 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1015
    | exact resolve eq1015 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1103 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1009 X0 X1 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1009
    | exact resolve eq1009 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1104 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) (M.op X3 X3)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1008 X0 X1 X3 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1008
    | exact resolve eq1008 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1105 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (σ y))) (σ y))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1007 X0 X2 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1007
    | exact resolve eq1007 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1119 : (σ y) = (τ (τ (σ y))) := by
    first
    | (have i₁ := eq1057
       have i₂ := eq985 (τ (τ sF3))
       grind)
    | exact superpose eq985 eq1057
    | exact resolve eq1057 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1122 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq1054
       have i₂ := eq985 (σ sF3)
       grind)
    | exact superpose eq985 eq1054
    | exact resolve eq1054 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1125 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq1051
       have i₂ := eq985 (τ sF3)
       grind)
    | exact superpose eq985 eq1051
    | exact resolve eq1051 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1132 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq986 eq1093
    | exact resolve eq1093 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1135 : (M.op (M.op x y) (σ y)) = (M.op (M.op x (σ y)) (M.op y (σ y))) := by
    first
    | (have i₁ := eq1098 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1098
    | exact resolve eq1098 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1136 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1 x
       have i₂ := eq985 x
       grind)
    | exact superpose eq985 eq1104
    | exact resolve eq1104 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq1104
  have eq1142 : (σ y) = (τ y) := by
    first
    | exact superpose eq39 eq1119
    | exact resolve eq1119 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1150 : y = (σ y) := by
    first
    | exact superpose eq39 eq1125
    | exact resolve eq1125 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1125
  have eq1154 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq986 eq1132
    | exact resolve eq1132 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1156 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1136 eq1105
    | exact resolve eq1105 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1158 : (M.op (M.op x y) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq1136 eq1135
    | exact resolve eq1135 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1168 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1150 eq26
    | exact resolve eq26 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1174 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1150 eq977
    | exact resolve eq977 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1178 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq1150 eq986
    | exact resolve eq986 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1179 : ∀ X0 X1 : G, y ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1150 eq987
    | (have j0 := eq987 X0 X1
       grind)
    | (have r₁ := eq987 y X1
       have r₂ := eq1150
       grind)
    | exact resolve eq987 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1181 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 := by
    intro X0
    first
    | exact superpose eq1150 eq1025
    | exact resolve eq1025 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1182 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ y = X2 := by
    intro X2 X3
    first
    | exact superpose eq1150 eq1042
    | (have j0 := eq1042 X2 X3
       grind)
    | exact resolve eq1042 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1183 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1060
    | (have j0 := eq1060 X0 X1
       grind)
    | exact resolve eq1060 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1061
    | (have j0 := eq1061 X0 X1
       grind)
    | exact resolve eq1061 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1185 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1069
    | (have j0 := eq1069 X0 X1
       grind)
    | exact resolve eq1069 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1192 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ y = (σ x) := by
    intro X0
    first
    | exact superpose eq1150 eq1087
    | (have j0 := eq1087 X0
       grind)
    | exact resolve eq1087 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1193 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (σ x) := by
    first
    | exact superpose eq1150 eq1088
    | exact resolve eq1088 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1195 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X1) (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1103
    | exact resolve eq1103 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1201 : y = (σ y) := by
    first
    | exact superpose eq1150 eq1122
    | exact resolve eq1122 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1202 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq1150 eq1136
    | exact resolve eq1136 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1203 : y = (τ y) := by
    first
    | exact superpose eq1150 eq1142
    | exact resolve eq1142 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1208 : (σ x) = (M.op (M.op (σ x) (σ y)) y) := by
    first
    | exact superpose eq1150 eq1154
    | exact resolve eq1154 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1209 : (M.op (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1150 eq1158
    | exact resolve eq1158 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1211 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 y) (M.op (M.op X0 y) y))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq1150 eq1156
    | exact resolve eq1156 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq1156
  have eq1226 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1209
       have i₂ := eq1181 x
       grind)
    | exact superpose eq1181 eq1209
    | (have j1 := eq1181 x
       grind)
    | exact resolve eq1209 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1228 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 y) X0)) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1211 X0 X2
       have i₂ := eq1181 X0
       grind)
    | exact superpose eq1181 eq1211
    | exact resolve eq1211 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1318 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1228 X1 (M.op X0 y)
       have i₂ := eq1181 X0
       grind)
    | exact superpose eq1181 eq1228
    | exact resolve eq1228 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 : G, x = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1228 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1228
    | (have j0 := eq1228 X0 x
       grind)
    | exact resolve eq1228 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq1226 eq1228
    | exact resolve eq1228 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1168 eq1228
    | exact resolve eq1228 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1208 eq1228
    | exact resolve eq1228 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq1226 eq1195
    | exact resolve eq1195 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1437 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1208 eq1195
    | exact resolve eq1195 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1733 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq1202 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1202
    | (have j0 := eq1202 X0 x
       grind)
    | exact resolve eq1202 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 y) (M.op X1 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1195 (M.op X0 X1) X2
       have i₂ := eq1202 X0 X1
       grind)
    | exact superpose eq1202 eq1195
    | exact resolve eq1195 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1952 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1174 X1 X2
       have i₂ := eq1318 (M.op X1 X2) X0
       grind)
    | exact superpose eq1318 eq1174
    | exact resolve eq1174 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq2425 : (M.op (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1193
       have i₂ := eq1182 x sF0
       grind)
    | exact superpose eq1182 eq1193
    | (have j1 := eq1182 (σ x) x
       grind)
    | exact resolve eq1193 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq3044 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 x) y)) = X0 := by
    intro X0
    first
    | exact superpose eq1733 eq1228
    | exact resolve eq1228 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq1733
  have eq3081 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op X1 x) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3044 X1
       have i₂ := eq1318 (M.op X1 x) X0
       grind)
    | exact superpose eq1318 eq3044
    | exact resolve eq3044 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq3044
  have eq9092 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq1183 X0 X1
       grind)
    | exact superpose eq1183 eq10
    | (have j1 := eq1183 X0 X1
       grind)
    | exact resolve eq10 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq9155 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1184
    | (have j0 := eq1184 X0 (τ X0)
       grind)
    | exact resolve eq1184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq14010 : ∀ X0 : G, (τ x) = (k (τ X0) (τ (M.op (M.op x y) X0))) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1319 eq1185
    | (have j0 := eq1185 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq1185 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq1319
  have eq14119 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq9092 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9092
    | (have j0 := eq9092 x X0
       grind)
    | exact resolve eq9092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9092
  have eq14188 : (τ (σ x)) = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1322 eq14119
    | (have j0 := eq14119 (M.op (M.op (σ x) (σ y)) (σ x))
       grind)
    | exact resolve eq14119 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14119
  have eq14231 : x = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq38 eq14188
    | exact resolve eq14188 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14188
  have eq15728 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X1 (M.op x y)) X0) (M.op (M.op X1 y) x)) := by
    intro X0 X1
    first
    | exact superpose eq1226 eq1736
    | exact resolve eq1736 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq17720 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq14231 eq48
    | exact resolve eq48 eq14231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq14231
  have eq17755 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have j1 := eq1179 (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)
       grind)
    | (have r₁ := eq17720
       have r₂ := eq1179 (M.op (M.op (σ x) (σ y)) (σ x)) x
       grind)
    | exact resolve eq17720 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720
  have eq17763 : (σ x) = (k (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq17755
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17755
    | exact resolve eq17755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17755
  have eq17780 : (τ (σ x)) = (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq17763 eq128
    | exact resolve eq128 eq17763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17763
  have eq17781 : x = (k x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq38 eq17780
    | exact resolve eq17780 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17780
  have eq17806 : x = (M.op x (τ (M.op (M.op (σ x) (σ y)) (σ x)))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq17781 eq1182
    | (have j0 := eq1182 (τ (M.op (M.op (σ x) (σ y)) (σ x))) x
       grind)
    | exact resolve eq1182 eq17781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq17781
  have eq23266 : (M.op (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq2425 eq10
    | exact resolve eq10 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq23328 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38 eq9155
    | exact resolve eq9155 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9155
  have eq28678 : (k (M.op (σ (M.op x y)) (σ x)) (σ x)) = (σ (M.op (M.op (M.op x y) x) x)) ∨ x = y ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq23266 eq23328
    | exact resolve eq23328 eq23266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23328
  have eq28679 : (k (M.op (σ (M.op x y)) (σ x)) (σ x)) = (σ (M.op (M.op (M.op x y) x) x)) ∨ x = y ∨ y = (σ x) := by grind
  clear eq28678
  have eq28692 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq1435 eq28679
    | exact resolve eq28679 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq28679
  have eq28700 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have i₁ := eq28692
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28692
    | exact resolve eq28692 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28692
  have eq28704 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq20 eq28700
    | exact resolve eq28700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28700
  have eq28706 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ x))) (τ (σ x))) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq28704 eq128
    | exact resolve eq128 eq28704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq28704
  have eq28729 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq38 eq28706
    | exact resolve eq28706 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28706
  have eq28730 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq37 eq28729
    | exact resolve eq28729 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq28729
  have eq39104 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ x = y ∨ y = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq23266 eq28730
    | exact resolve eq28730 eq23266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23266 eq28730
  have eq39145 : (M.op x y) = (k (M.op (M.op x y) x) x) ∨ x = y ∨ y = (σ x) := by grind
  clear eq39104
  have eq39205 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq39145 eq1192
    | exact resolve eq1192 eq39145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq39145
  have eq39228 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y := by grind
  clear eq39205
  have eq39242 : (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq39228
    | exact resolve eq39228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39228
  have eq54458 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op X0 (M.op x X0)) x) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq17806 eq1952
    | exact resolve eq1952 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17806
  have eq54516 : (M.op (M.op x y) x) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq54458 x
       have i₂ := eq1321 x
       grind)
    | exact superpose eq1321 eq54458
    | exact resolve eq54458 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321 eq54458
  have eq88910 : y = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq54516 eq11
    | exact resolve eq11 eq54516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54516
  have eq127479 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq88910 eq11
    | exact resolve eq11 eq88910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88910
  have eq127666 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq127479
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq127479
    | exact resolve eq127479 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127479
  have eq127709 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq127666 eq39242
    | exact resolve eq39242 eq127666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127666
  have eq127778 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1437 eq127709
    | exact resolve eq127709 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq127709
  have eq127785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y ∨ y = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1168 eq127778
    | exact resolve eq127778 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127778
  have eq127786 : y = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have r₁ := eq127785
       have r₂ := eq27
       grind)
    | exact resolve eq127785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127785
  have eq127823 : (σ x) = (M.op (σ x) y) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq127786 eq1322
    | exact resolve eq1322 eq127786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq127786
  have eq127998 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq1168 eq127823
    | exact resolve eq127823 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127823
  have eq128102 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq127998 eq27
    | exact resolve eq27 eq127998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127998
  have eq392230 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x (M.op x y)) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq15728 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15728
    | (have j0 := eq15728 X0 x
       grind)
    | exact resolve eq15728 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728
  have eq392487 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) (M.op X0 y)) (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq392230 eq1952
    | exact resolve eq1952 eq392230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq392230
  have eq392891 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq392487 (M.op X0 y)
       have i₂ := eq1181 X0
       grind)
    | exact superpose eq1181 eq392487
    | exact resolve eq392487 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq392487
  have eq429028 : ∀ X0 : G, (σ (τ x)) = (k X0 (σ (τ (M.op (M.op x y) X0)))) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq14010 eq49
    | (have j1 := eq14010 X0
       grind)
    | exact resolve eq49 eq14010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq14010
  have eq429030 : ∀ X0 : G, (σ (τ x)) = (k X0 (M.op (M.op x y) X0)) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq429028 X0
       have i₂ := eq11 (M.op sF0 X0)
       grind)
    | exact superpose eq11 eq429028
    | (have j0 := eq429028 X0
       grind)
    | exact resolve eq429028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429028
  have eq429041 : ∀ X0 : G, x = (k X0 (M.op (M.op x y) X0)) ∨ y = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq429030 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq429030
    | (have j0 := eq429030 X0
       grind)
    | exact resolve eq429030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429030
  have eq429047 : ∀ X0 X1 : G, x = (k (M.op X1 (M.op (M.op X0 x) X1)) X0) ∨ y = X0 := by
    intro X0 X1
    first
    | exact superpose eq3081 eq429041
    | exact resolve eq429041 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081 eq429041
  have eq437907 : x = (k (M.op (M.op x (M.op x y)) (M.op x y)) (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq392891 eq429047
    | (have j0 := eq429047 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq429047 eq392891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392891 eq429047
  have eq438138 : x = (k (M.op (M.op x y) y) (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq437907
       have i₂ := eq1195 x sF0
       grind)
    | exact superpose eq1195 eq437907
    | exact resolve eq437907 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq437907
  have eq438189 : x = (k x (M.op (M.op x y) x)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1226 eq438138
    | exact resolve eq438138 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq438138
  have eq438205 : x = (k x (M.op (M.op x y) x)) := by
    first
    | (have j1 := eq1179 (M.op (M.op x y) x) x
       grind)
    | (have r₁ := eq438189
       have r₂ := eq1179 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq438189 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq438189
  have eq438389 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq438205 eq1186
    | (have j0 := eq1186 x (M.op (M.op x y) x)
       grind)
    | exact resolve eq1186 eq438205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq438205
  have eq438403 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq438389
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq438389
    | exact resolve eq438389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438389
  have eq455020 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op x y) x)) (σ x)) ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq438403 eq1323
    | exact resolve eq1323 eq438403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq438403
  have eq463397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y ∨ y = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq455020 eq39242
    | exact resolve eq39242 eq455020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455020
  have eq463414 : y = (σ (M.op (M.op x y) x)) ∨ x = y ∨ y = (σ x) := by
    first
    | (have r₁ := eq463397
       have r₂ := eq27
       grind)
    | exact resolve eq463397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463397
  have eq463423 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (σ x) ∨ x = y ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq463414 eq39242
    | exact resolve eq39242 eq463414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39242 eq463414
  have eq463438 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (σ x) ∨ x = y := by grind
  clear eq463423
  have eq463452 : (σ (M.op x y)) = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq463438
       have i₂ := eq1178 sF2
       grind)
    | exact superpose eq1178 eq463438
    | exact resolve eq463438 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463438
  have eq463455 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq463452
       have r₂ := eq128102
       grind)
    | exact resolve eq463452 eq128102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128102 eq463452
  have eq463459 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq463455 eq38
    | exact resolve eq38 eq463455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq463455
  have eq463937 : x = y ∨ x = y := by
    first
    | (have i₁ := eq463459
       have i₂ := eq1203
       grind)
    | exact superpose eq1203 eq463459
    | exact resolve eq463459 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq463459
  have eq463938 : x = y := by grind
  clear eq463937
  have eq464078 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq463938
       grind)
    | exact superpose eq463938 eq18
    | exact resolve eq18 eq463938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq464081 : (M.op (σ x) (σ y)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq463938
       grind)
    | exact superpose eq463938 eq1168
    | exact resolve eq1168 eq463938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq464084 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1178 X0
       have i₂ := eq463938
       grind)
    | exact superpose eq463938 eq1178
    | exact resolve eq1178 eq463938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq464101 : x = (σ x) := by
    first
    | (have i₁ := eq1201
       have i₂ := eq463938
       grind)
    | exact superpose eq463938 eq1201
    | exact resolve eq1201 eq463938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq463938
  have eq530201 : x = (σ x) := by
    first
    | (have i₁ := eq464101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq464101
    | exact resolve eq464101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464101
  have eq533720 : x = (M.op x y) := by
    first
    | (have i₁ := eq464078
       have i₂ := eq464084 x
       grind)
    | exact superpose eq464084 eq464078
    | exact resolve eq464078 eq464084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464078
  have eq544556 : x = (σ x) := by
    first
    | exact superpose eq530201 eq22
    | exact resolve eq22 eq530201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq544562 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | exact superpose eq530201 eq464081
    | exact resolve eq464081 eq530201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464081 eq530201
  have eq552671 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq533720 eq20
    | exact resolve eq20 eq533720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq533720
  have eq563117 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq544562
       have i₂ := eq464084 x
       grind)
    | exact superpose eq464084 eq544562
    | exact resolve eq544562 eq464084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464084 eq544562
  have eq569723 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq552671
       have i₂ := eq544556
       grind)
    | exact superpose eq544556 eq552671
    | exact resolve eq552671 eq544556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544556 eq552671
  have eq574955 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq563117 eq27
    | exact resolve eq27 eq563117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq563117
  have eq583375 : False := by grind
  exact eq583375
