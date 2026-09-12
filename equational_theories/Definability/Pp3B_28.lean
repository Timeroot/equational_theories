import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq69 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq72 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq66 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq72 X0 X0 x
       grind)
    | exact superpose eq72 eq61
    | exact resolve eq61 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq188 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 X0 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq72
    | exact resolve eq72 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq177
  have eq201 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq188 X0
       grind)
    | exact resolve eq12 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq9
    | exact resolve eq9 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq208 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq71 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq206 X0 X1
       have i₂ := eq71 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq71 eq206
    | exact resolve eq206 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq206
  have eq216 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq207 X1 (σ X0)
       grind)
    | exact superpose eq207 eq28
    | exact resolve eq28 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq207 X1 (τ X0)
       grind)
    | exact superpose eq207 eq17
    | exact resolve eq17 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq224 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219
    | exact resolve eq219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq227 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216
    | exact resolve eq216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq470 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq9
    | exact resolve eq9 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq477 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq470
    | exact resolve eq470 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq470
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq224 (σ (M.op X0 X0)) X0
       have i₂ := eq658 (σ (M.op X0 X0))
       grind)
    | exact superpose eq658 eq224
    | (have j1 := eq658 (σ (M.op X0 X0))
       grind)
    | exact resolve eq224 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq704 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq658 (τ X0)
       grind)
    | exact superpose eq658 eq17
    | (have j1 := eq658 (τ X0)
       grind)
    | exact resolve eq17 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq658
  have eq718 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq735 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq704 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | (have j0 := eq704 X0
       grind)
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq747 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq1472 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq747 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq747 X0 X1
       grind)
    | exact superpose eq747 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq747 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq747 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq747 X0 X1
       grind)
    | exact resolve eq13 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq1482 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1472 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1483 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1483 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1483
    | (have j0 := eq1483 X0 X1
       grind)
    | exact resolve eq1483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1527 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 (σ (M.op X0 X0)) X1
       have i₂ := eq718 X0
       grind)
    | exact superpose eq718 eq477
    | exact resolve eq477 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq6195 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq735 X0
       grind)
    | exact superpose eq735 eq10
    | (have j1 := eq735 X0
       grind)
    | exact resolve eq10 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq7486 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1489 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1489
    | (have j0 := eq1489 (τ X1) X1
       grind)
    | exact resolve eq1489 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq7527 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7486 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7486
    | (have j0 := eq7486 X0 X1
       grind)
    | exact resolve eq7486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7486
  have eq7560 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7527 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7527
    | (have j0 := eq7527 X0 X1
       grind)
    | exact resolve eq7527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7527
  have eq7568 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7560 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7560
    | (have j0 := eq7560 X0 X1
       grind)
    | exact resolve eq7560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7560
  have eq7576 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7568 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7568
    | (have j0 := eq7568 X0 X1
       grind)
    | exact resolve eq7568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7568
  have eq7628 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1489 X0 X1
       have i₂ := eq7576 X1 X0
       grind)
    | exact superpose eq7576 eq1489
    | (have j0 := eq1489 X0 X1
       have j1 := eq7576 X0 (σ X0)
       grind)
    | exact resolve eq1489 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq7576
  have eq90069 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq92546 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90069 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq90069
    | (have j0 := eq90069 (σ X0)
       grind)
    | exact resolve eq90069 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq90069
  have eq92668 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq92546 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92546
    | (have j0 := eq92546 X0
       grind)
    | exact resolve eq92546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92546
  have eq92719 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq92668 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92668
    | (have j0 := eq92668 X0
       grind)
    | exact resolve eq92668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92668
  have eq632257 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7628 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7628
  have eq636853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq632257 x y
       grind)
    | exact superpose eq632257 eq16
    | (have j1 := eq632257 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq632257 x y
       grind)
    | exact resolve eq16 eq632257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632257
  have eq637336 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq636853
  have eq643720 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq227 X0 (σ x)
       have i₂ := eq637336
       grind)
    | exact superpose eq637336 eq227
    | exact resolve eq227 eq637336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq637336
  have eq644125 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq643720 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq643720
    | exact resolve eq643720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643720
  have eq644173 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq644125 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq644125 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq644125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644125
  have eq644490 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq92719 x
       have i₂ := eq644173 x
       grind)
    | exact superpose eq644173 eq92719
    | (have j0 := eq92719 x
       grind)
    | (have r₁ := eq92719 x
       have r₂ := eq644173 x
       grind)
    | exact resolve eq92719 eq644173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92719 eq644173
  have eq645019 : x = (M.op x x) := by grind
  clear eq644490
  have eq645166 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq477 x X0
       have i₂ := eq645019
       grind)
    | exact superpose eq645019 eq477
    | exact resolve eq477 eq645019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq645181 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1527 x X0
       have i₂ := eq645019
       grind)
    | exact superpose eq645019 eq1527
    | exact resolve eq1527 eq645019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527 eq645019
  have eq645550 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645166 y
       grind)
    | exact superpose eq645166 eq16
    | exact resolve eq16 eq645166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645166
  have eq652268 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq645550
       have i₂ := eq645181 (σ y)
       grind)
    | exact superpose eq645181 eq645550
    | (have r₁ := eq645550
       have r₂ := eq645181 (σ y)
       grind)
    | exact resolve eq645550 eq645181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645181 eq645550
  have eq652737 : False := by grind
  exact eq652737

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_pyy_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq230 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq349 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq358 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq358
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq362 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq364 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq349 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq349
    | exact resolve eq349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq382 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq361 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq361
    | (have j0 := eq361 x y
       grind)
    | exact resolve eq361 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq361
    | (have j0 := eq361 (σ x) (σ y)
       grind)
    | exact resolve eq361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq382 eq14
    | exact resolve eq14 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq588 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq584 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq590 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq588 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq588 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq3056 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362 eq52
    | exact resolve eq52 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3071 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3056 eq362
    | exact resolve eq362 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq3056
  have eq3085 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3071 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq3071
       grind)
    | exact resolve eq13 eq3071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3090 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq3085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3222 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq364 X0 X0 x
       grind)
    | exact superpose eq364 eq52
    | exact resolve eq52 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3262 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq364 X0 X0 X0
       have i₂ := eq3222 X0
       grind)
    | exact superpose eq3222 eq364
    | exact resolve eq364 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3356 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3090 eq590
    | (have j0 := eq590 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq590 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3371 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3071 eq3356
    | (have j0 := eq3356 X0
       grind)
    | exact resolve eq3356 eq3071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071 eq3356
  have eq3372 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq3371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3443 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3372 eq35
    | exact resolve eq35 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3444 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3372 eq36
    | exact resolve eq36 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3467 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3090 eq3444
    | exact resolve eq3444 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3468 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3090 eq3443
    | exact resolve eq3443 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090 eq3443
  have eq3484 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3467
       grind)
    | exact superpose eq3467 eq16
    | exact resolve eq16 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4733 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3262 X0
       grind)
    | exact superpose eq3262 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3262 X0
       grind)
    | exact resolve eq13 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4749 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4733 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4793 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3222 X0
       have i₂ := eq4749 X1 X0
       grind)
    | exact superpose eq4749 eq3222
    | exact resolve eq3222 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3222
  have eq4828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq590 (M.op X0 X0) X1
       have i₂ := eq4749 X0 (M.op X0 X0)
       grind)
    | exact superpose eq4749 eq590
    | (have j0 := eq590 (M.op X0 X0) X1
       grind)
    | exact resolve eq590 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq4849 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4828 X0 X1
       have i₂ := eq3262 X0
       grind)
    | exact superpose eq3262 eq4828
    | (have j0 := eq4828 X0 X1
       grind)
    | exact resolve eq4828 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262 eq4828
  have eq4850 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4849 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849
  have eq4955 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 (M.op X1 X1)
       have i₂ := eq4850 X1 X0
       grind)
    | exact superpose eq4850 eq230
    | exact resolve eq230 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq4850
  have eq7242 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4793 (τ X0) x
       have i₂ := eq4955 X0 x
       grind)
    | exact superpose eq4955 eq4793
    | exact resolve eq4793 eq4955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4793 eq4955
  have eq24812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq24820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24812
    | exact resolve eq24812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24812
  have eq24831 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24820
       have r₂ := eq27
       grind)
    | exact resolve eq24820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24820
  have eq24835 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24831
    | exact resolve eq24831 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq24837 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24835 eq3484
    | exact resolve eq3484 eq24835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484 eq24835
  have eq24916 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24837
    | exact resolve eq24837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24837
  have eq24917 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24916
  have eq24927 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3467
       have i₂ := eq24917
       grind)
    | exact superpose eq24917 eq3467
    | exact resolve eq3467 eq24917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24974 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq364 y y x
       have i₂ := eq24917
       grind)
    | exact superpose eq24917 eq364
    | exact resolve eq364 eq24917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24979 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24974 X0
       have i₂ := eq361 y X0
       grind)
    | (have i₁ := eq24974 X0
       have i₂ := eq361 y (M.op y X0)
       grind)
    | exact superpose eq361 eq24974
    | exact resolve eq24974 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24974
  have eq25006 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24927
    | exact resolve eq24927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24927
  have eq25242 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25006 eq364
    | exact resolve eq364 eq25006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq25247 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25242 X0
       have i₂ := eq361 sF3 (M.op sF3 X0)
       grind)
    | (have i₁ := eq25242 x
       have i₂ := eq361 sF3 x
       grind)
    | exact superpose eq361 eq25242
    | exact resolve eq25242 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25242
  have eq25795 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq24979 X0
       grind)
    | exact superpose eq24979 eq14
    | exact resolve eq14 eq24979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26773 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25247 eq14
    | exact resolve eq14 eq25247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27451 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25795 X0
       have i₂ := eq24917
       grind)
    | exact superpose eq24917 eq25795
    | exact resolve eq25795 eq24917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24917 eq25795
  have eq27550 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27451
  have eq27557 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24979 X0
       have i₂ := eq27550 X0
       grind)
    | exact superpose eq27550 eq24979
    | exact resolve eq24979 eq27550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24979 eq27550
  have eq27644 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27557 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27557
  have eq27659 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27644 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27644
    | (have j0 := eq27644 x
       grind)
    | exact resolve eq27644 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27644
  have eq27795 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27659 eq51
    | exact resolve eq51 eq27659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27804 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27659 eq384
    | exact resolve eq384 eq27659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27828 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq27795 X0
       have i₂ := eq361 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq27795 x
       have i₂ := eq361 sF2 x
       grind)
    | exact superpose eq361 eq27795
    | exact resolve eq27795 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27795
  have eq27949 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27804 eq4749
    | exact resolve eq4749 eq27804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749
  have eq28483 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25006 eq26773
    | exact resolve eq26773 eq25006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25006 eq26773
  have eq28584 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28483
  have eq28591 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28584 eq25247
    | exact resolve eq25247 eq28584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25247 eq28584
  have eq28679 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28591
  have eq28697 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28679
    | (have j0 := eq28679 (σ x)
       grind)
    | exact resolve eq28679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28679
  have eq28831 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28697 eq27
    | exact resolve eq27 eq28697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28697
  have eq29510 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27804 eq27828
    | exact resolve eq27828 eq27804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27804
  have eq29519 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27828 eq14
    | exact resolve eq14 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27828
  have eq29562 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29510
  have eq29577 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq29519
    | (have j0 := eq29519 X0
       grind)
    | exact resolve eq29519 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29519
  have eq29580 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq29562
    | exact resolve eq29562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29562
  have eq29610 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29580 eq27659
    | exact resolve eq27659 eq29580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27659
  have eq29619 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29610
  have eq30255 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29577 eq3372
    | exact resolve eq3372 eq29577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq29577
  have eq31669 : (σ y) = (k (σ y) (σ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29580 eq30255
    | exact resolve eq30255 eq29580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29580 eq30255
  have eq31691 : (σ y) = (k (σ y) (σ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq31669
  have eq31703 : (σ y) = (σ (k y (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36 eq31691
    | exact resolve eq31691 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq31691
  have eq31971 : (σ x) = (σ (k y (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29619 eq31703
    | exact resolve eq31703 eq29619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29619 eq31703
  have eq32044 : (σ x) = (σ (k y (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq31971
  have eq34961 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27949 eq32044
    | exact resolve eq32044 eq27949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27949 eq32044
  have eq34995 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq34961
  have eq35032 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34995
       have i₂ := eq3467
       grind)
    | exact superpose eq3467 eq34995
    | exact resolve eq34995 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq34995
  have eq35110 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35032 eq7242
    | exact resolve eq7242 eq35032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7242 eq35032
  have eq35166 : y = (M.op (τ (σ x)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq35110
    | exact resolve eq35110 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35110
  have eq35173 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq35166
    | exact resolve eq35166 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq35166
  have eq35174 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35173
    | exact resolve eq35173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35173
  have eq35175 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq35174
  have eq35176 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35175 eq20
    | exact resolve eq20 eq35175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35175
  have eq35324 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35176
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35176
    | exact resolve eq35176 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35176
  have eq35634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35324 eq28831
    | (have r₁ := eq28831
       have r₂ := eq35324
       grind)
    | exact resolve eq28831 eq35324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28831
  have eq35662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35634
  have eq35663 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35662
  have eq35743 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35663 eq51
    | exact resolve eq51 eq35663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq35752 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35663 eq384
    | exact resolve eq384 eq35663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq35663
  have eq35796 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35743 X0
       have i₂ := eq361 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq35743 x
       have i₂ := eq361 sF2 x
       grind)
    | exact superpose eq361 eq35743
    | exact resolve eq35743 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35743
  have eq39525 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35752 eq35796
    | exact resolve eq35796 eq35752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35752 eq35796
  have eq39597 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39525
  have eq39620 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39597
    | exact resolve eq39597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39597
  have eq39909 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39620 eq27
    | exact resolve eq27 eq39620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39620
  have eq39976 : x = (M.op x y) := by
    first
    | (have r₁ := eq39909
       have r₂ := eq35324
       grind)
    | exact resolve eq39909 eq35324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35324 eq39909
  have eq39980 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq39976 eq20
    | exact resolve eq20 eq39976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq40039 : x = (M.op x x) := by
    first
    | exact superpose eq39976 eq382
    | exact resolve eq382 eq39976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq40040 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq39976 eq400
    | exact resolve eq400 eq39976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq40080 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq40040 X0
       have i₂ := eq361 x X0
       grind)
    | (have i₁ := eq40040 X0
       have i₂ := eq361 x (M.op x X0)
       grind)
    | exact superpose eq361 eq40040
    | exact resolve eq40040 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq40040
  have eq40136 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39980
    | exact resolve eq39980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39980
  have eq40189 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40136 eq26
    | exact resolve eq26 eq40136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40386 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3468
       have i₂ := eq40039
       grind)
    | exact superpose eq40039 eq3468
    | exact resolve eq3468 eq40039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq40462 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40136 eq40386
    | exact resolve eq40386 eq40136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40386
  have eq40475 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq40462
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40462
    | exact resolve eq40462 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40462
  have eq40478 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40136 eq40475
    | exact resolve eq40475 eq40136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40475
  have eq41029 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq40080 X0
       grind)
    | exact superpose eq40080 eq14
    | exact resolve eq14 eq40080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40080
  have eq41086 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41029 X0
       have i₂ := eq40039
       grind)
    | exact superpose eq40039 eq41029
    | exact resolve eq41029 eq40039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40039 eq41029
  have eq41118 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq41086 y
       grind)
    | exact superpose eq41086 eq18
    | (have j1 := eq41086 y
       grind)
    | exact resolve eq18 eq41086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq41086
  have eq41250 : x = y := by
    first
    | exact superpose eq39976 eq41118
    | exact resolve eq41118 eq39976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39976 eq41118
  have eq41309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq41250
       grind)
    | exact superpose eq41250 eq24
    | exact resolve eq24 eq41250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq41250
  have eq41471 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41309
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41309
    | exact resolve eq41309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41309
  have eq41536 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40136 eq41471
    | exact resolve eq41471 eq40136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40136 eq41471
  have eq41845 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41536 eq40189
    | exact resolve eq40189 eq41536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40189 eq41536
  have eq41848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40478 eq41845
    | exact resolve eq41845 eq40478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40478 eq41845
  have eq41902 : False := by grind
  exact eq41902

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq230 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq344 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq358 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq358
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq362 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq364 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq349 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq349
    | exact resolve eq349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq485 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq230
    | exact resolve eq230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq579 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq587 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq589 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq579 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq591 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq589 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq589 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq589 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1181 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq591
    | (have j0 := eq591 (τ X0) X1
       grind)
    | exact resolve eq591 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1181 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1181
    | (have j0 := eq1181 X0 X1
       grind)
    | exact resolve eq1181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1195 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1189 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1189
    | (have j0 := eq1189 X0 X1
       grind)
    | exact resolve eq1189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1249 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (τ X0) X1
       have i₂ := eq485 X0 X0
       grind)
    | exact superpose eq485 eq1195
    | (have j0 := eq1195 (τ X0) X1
       grind)
    | exact resolve eq1195 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq1195
  have eq3086 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362 eq61
    | exact resolve eq61 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3101 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3086 eq362
    | exact resolve eq362 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq3086
  have eq3119 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3101 eq14
    | exact resolve eq14 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3121 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3119 X0
       have i₂ := eq361 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3119 x
       have i₂ := eq361 (M.op sF4 sF4) x
       grind)
    | exact superpose eq361 eq3119
    | exact resolve eq3119 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3357 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq364 X0 X0 x
       grind)
    | exact superpose eq364 eq61
    | exact resolve eq61 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3393 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq364 X0 X0 X0
       have i₂ := eq3357 X0
       grind)
    | exact superpose eq3357 eq364
    | exact resolve eq364 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3433 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq587 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq587
    | (have j0 := eq587 (τ X0)
       grind)
    | exact resolve eq587 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3444 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3433 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3433
    | (have j0 := eq3433 X0
       grind)
    | exact resolve eq3433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq3451 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3444 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3444
    | (have j0 := eq3444 X0
       grind)
    | exact resolve eq3444 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3814 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq344 X0 X0 x X0 X2
       have i₂ := eq364 X0 X0 x
       grind)
    | exact superpose eq364 eq344
    | exact resolve eq344 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq4933 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3393 X0
       grind)
    | exact superpose eq3393 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3393 X0
       grind)
    | exact resolve eq13 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq4982 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 (M.op X1 X1)
       have i₂ := eq4943 X1 (σ X0)
       grind)
    | exact superpose eq4943 eq330
    | exact resolve eq330 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq4988 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4982 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4982
    | exact resolve eq4982 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq25479 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3121 eq353
    | exact resolve eq353 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq25480 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3121 eq14
    | exact resolve eq14 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq25535 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25480 X0
       have i₂ := eq3393 sF4
       grind)
    | exact superpose eq3393 eq25480
    | exact resolve eq25480 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq25480
  have eq25536 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq25479
       have i₂ := eq3814 sF4 sF4
       grind)
    | exact superpose eq3814 eq25479
    | exact resolve eq25479 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814 eq25479
  have eq25543 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq25536 eq60
    | exact resolve eq60 eq25536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq25536
  have eq25650 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq25535 eq364
    | exact resolve eq364 eq25535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq25677 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq25535 eq25650
    | exact resolve eq25650 eq25535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25535 eq25650
  have eq27092 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq25677 X0 X1
       grind)
    | exact superpose eq25677 eq14
    | exact resolve eq14 eq25677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq28566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq28565
    | exact resolve eq28565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28565
  have eq28577 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28566
       have r₂ := eq27
       grind)
    | exact resolve eq28566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28566
  have eq28601 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28577 eq361
    | exact resolve eq361 eq28577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28577
  have eq28658 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28601 eq4943
    | exact resolve eq4943 eq28601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28601
  have eq28728 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq4988 X0 X1
       have i₂ := eq28658 (M.op X1 X1)
       grind)
    | exact superpose eq28658 eq4988
    | (have j1 := eq28658 X1
       grind)
    | exact resolve eq4988 eq28658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988 eq28658
  have eq28775 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq28728
    | (have j0 := eq28728 X0 X1
       grind)
    | exact resolve eq28728 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28728
  have eq28783 : ∀ X0 X1 : G, y = (M.op y x) ∨ (k X1 (σ y)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28775 X0 X1
       have j1 := eq13 X1 (σ y)
       grind)
    | (have r₁ := eq28775 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq28775 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28775
  have eq28806 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 y x
       have i₂ := eq28783 X0 X1
       grind)
    | exact superpose eq28783 eq361
    | (have j1 := eq28783 X1 X0
       grind)
    | exact resolve eq361 eq28783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq28783
  have eq29170 : ∀ X0 X1 X2 : G, (k X2 x) = X2 ∨ (k X1 (σ y)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4943 y X0
       have i₂ := eq28806 X1 X2
       grind)
    | exact superpose eq28806 eq4943
    | (have j1 := eq28806 X1 X2
       grind)
    | exact resolve eq4943 eq28806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943 eq28806
  have eq29669 : ∀ X0 X1 X2 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq591 x X0
       have i₂ := eq29170 X2 X1 x
       grind)
    | exact superpose eq29170 eq591
    | (have j0 := eq591 x X0
       have j1 := eq29170 X2 X1 X2
       grind)
    | exact resolve eq591 eq29170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq29170
  have eq29695 : ∀ X0 X1 X2 : G, (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq29669 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29669
  have eq29724 : ∀ X0 X1 X2 : G, (k X2 y) = X2 ∨ (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29695 X0 X1 X2
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29695
    | (have j0 := eq29695 X0 X1 X2
       grind)
    | exact resolve eq29695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29695
  have eq31116 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq587 y
       have i₂ := eq29724 X1 X0 y
       grind)
    | exact superpose eq29724 eq587
    | (have j0 := eq587 y
       have j1 := eq29724 X1 X0 x
       grind)
    | exact resolve eq587 eq29724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq29724
  have eq31147 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31116
  have eq31176 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31147 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31147
    | (have j0 := eq31147 X0 X1
       grind)
    | exact resolve eq31147 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31147
  have eq31236 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31176 X0 X1
       have j1 := eq13 X1 (σ x)
       grind)
    | (have r₁ := eq31176 X0 X1
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq31176 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31176
  have eq31308 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X0 X1
       have i₂ := eq31236 (k X0 X0) X1
       grind)
    | exact superpose eq31236 eq1249
    | (have j0 := eq1249 (σ x) X0
       have j1 := eq31236 X1 X1
       grind)
    | exact resolve eq1249 eq31236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31309 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 X0
       have i₂ := eq31236 (k X0 X0) x
       grind)
    | exact superpose eq31236 eq3451
    | (have j0 := eq3451 (σ x)
       have j1 := eq31236 X0 x
       grind)
    | (have r₁ := eq3451 (σ x)
       have r₂ := eq31236 X0 (σ x)
       grind)
    | (have r₁ := eq3451 (σ y)
       have r₂ := eq31236 (σ y) x
       grind)
    | exact resolve eq3451 eq31236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31236
  have eq31342 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq31309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31309
  have eq31343 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31308
  have eq31368 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq31343
    | (have j0 := eq31343 X0 X1
       grind)
    | exact resolve eq31343 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31343
  have eq31429 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25543
       have i₂ := eq31342 (M.op sF2 sF2)
       grind)
    | exact superpose eq31342 eq25543
    | (have j1 := eq31342 X0
       grind)
    | exact resolve eq25543 eq31342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25543 eq31342
  have eq31490 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq31429
    | (have j0 := eq31429 X0
       grind)
    | exact resolve eq31429 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31429
  have eq31549 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31490 eq3451
    | (have j0 := eq3451 (σ y)
       grind)
    | (have r₁ := eq3451 (σ y)
       have r₂ := eq31490 (σ y)
       grind)
    | exact resolve eq3451 eq31490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31490
  have eq31582 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31549
  have eq31683 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31582 eq27092
    | exact resolve eq27092 eq31582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582
  have eq31956 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31683 eq25677
    | exact resolve eq25677 eq31683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31683
  have eq32143 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31956 eq26
    | (have j1 := eq31956 (σ x)
       grind)
    | exact resolve eq26 eq31956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31956
  have eq32165 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32143
  have eq32187 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq32165 eq27
    | exact resolve eq27 eq32165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32165
  have eq33423 : ∀ X0 X1 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X0 X1
       have i₂ := eq31368 (k X0 X0) X1
       grind)
    | exact superpose eq31368 eq1249
    | (have j0 := eq1249 (σ y) X0
       have j1 := eq31368 X1 X1
       grind)
    | exact resolve eq1249 eq31368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq31368
  have eq33458 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33423
  have eq33484 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq33458
    | (have j0 := eq33458 X0 X1
       grind)
    | exact resolve eq33458 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33458
  have eq34066 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 x
       have i₂ := eq33484 X0 x
       grind)
    | exact superpose eq33484 eq3451
    | (have j0 := eq3451 x
       have j1 := eq33484 X0 x
       grind)
    | (have r₁ := eq3451 x
       have r₂ := eq33484 X0 x
       grind)
    | (have r₁ := eq3451 y
       have r₂ := eq33484 y x
       grind)
    | exact resolve eq3451 eq33484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33484
  have eq34099 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq34066 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34066
  have eq34945 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27092 x X0
       have i₂ := eq34099 X1
       grind)
    | exact superpose eq34099 eq27092
    | (have j1 := eq34099 X1
       grind)
    | exact resolve eq27092 eq34099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34099
  have eq35816 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 y
       have i₂ := eq34945 X0 y
       grind)
    | exact superpose eq34945 eq3451
    | (have j0 := eq3451 y
       have j1 := eq34945 X0 x
       grind)
    | (have r₁ := eq3451 y
       have r₂ := eq34945 X0 y
       grind)
    | exact resolve eq3451 eq34945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq34945
  have eq35849 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq35816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35816
  have eq36578 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27092 y X0
       have i₂ := eq35849 X1
       grind)
    | exact superpose eq35849 eq27092
    | (have j1 := eq35849 X1
       grind)
    | exact resolve eq27092 eq35849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27092 eq35849
  have eq56841 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25677 y X0
       have i₂ := eq36578 X0 X1
       grind)
    | exact superpose eq36578 eq25677
    | (have j1 := eq36578 X0 X1
       grind)
    | exact resolve eq25677 eq36578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25677 eq36578
  have eq58340 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq56841 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56841
  have eq58341 : y = (M.op x y) := by grind
  clear eq58340
  have eq58343 : y = (M.op x y) := by
    first
    | (have i₁ := eq58341
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58341
    | exact resolve eq58341 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58341
  have eq58699 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq58343 eq20
    | exact resolve eq20 eq58343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq58343
  have eq58941 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq58699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58699
    | exact resolve eq58699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq58699
  have eq58943 : False := by grind
  exact eq58943

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq446 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x X0 X1 y
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq466 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq466
    | exact resolve eq466 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq470 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq472 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq455 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq701 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq702 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq3086 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq470 eq61
    | exact resolve eq61 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3101 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3086 eq470
    | exact resolve eq470 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3119 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3101 eq14
    | exact resolve eq14 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3121 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3119 X0
       have i₂ := eq469 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3119 x
       have i₂ := eq469 (M.op sF4 sF4) x
       grind)
    | exact superpose eq469 eq3119
    | exact resolve eq3119 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3357 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq61
    | exact resolve eq61 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3393 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0 X0 X0
       have i₂ := eq3357 X0
       grind)
    | exact superpose eq3357 eq472
    | exact resolve eq472 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3812 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X1)) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq470 eq446
    | exact resolve eq446 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq3814 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq446 X0 X0 x X0 X2
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq446
    | exact resolve eq446 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq4933 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3393 X0
       grind)
    | exact superpose eq3393 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3393 X0
       grind)
    | exact resolve eq13 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq25709 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3121 eq464
    | exact resolve eq464 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq25710 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3121 eq14
    | exact resolve eq14 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq25765 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25710 X0
       have i₂ := eq3393 sF4
       grind)
    | exact superpose eq3393 eq25710
    | exact resolve eq25710 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq25710
  have eq25766 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq25709
       have i₂ := eq3814 sF4 sF4
       grind)
    | exact superpose eq3814 eq25709
    | exact resolve eq25709 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814 eq25709
  have eq26131 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq25766 eq60
    | exact resolve eq60 eq25766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq25766
  have eq26173 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq25765 eq3812
    | exact resolve eq3812 eq25765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq26236 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq25765 eq472
    | exact resolve eq472 eq25765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq26263 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq25765 eq26236
    | exact resolve eq26236 eq25765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26236
  have eq26771 : x = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op x y)) x) := by
    first
    | exact superpose eq26173 eq462
    | exact resolve eq462 eq26173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq26173
  have eq26826 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq25765 eq26771
    | exact resolve eq26771 eq25765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25765 eq26771
  have eq27302 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq26263 X0 X1
       grind)
    | exact superpose eq26263 eq14
    | exact resolve eq14 eq26263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq28266
    | exact resolve eq28266 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28266
  have eq28278 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28267
       have r₂ := eq27
       grind)
    | exact resolve eq28267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28267
  have eq28285 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28278 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq28278
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq28278
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq28278
       grind)
    | exact resolve eq12 eq28278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28278
  have eq28314 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq28285
  have eq28315 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq28314
  have eq28337 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq28315
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq28315
       have r₂ := eq13 x x
       grind)
    | exact resolve eq28315 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28315
  have eq28361 : (τ (σ y)) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28337 eq93
    | exact resolve eq93 eq28337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq28362 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28337 eq95
    | exact resolve eq95 eq28337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq28337
  have eq28375 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq28362
  have eq28383 : y = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq28361
    | exact resolve eq28361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28361
  have eq28387 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq28383
       have r₂ := eq13 x x
       grind)
    | exact resolve eq28383 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28383
  have eq28389 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq28387
       grind)
    | exact superpose eq28387 eq69
    | exact resolve eq69 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq28387
  have eq28420 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq28389
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28389
    | exact resolve eq28389 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28389
  have eq28501 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq469 y x
       have i₂ := eq28375
       grind)
    | exact superpose eq28375 eq469
    | exact resolve eq469 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28375
  have eq31097 : ∀ X0 : G, x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27302 y X0
       have i₂ := eq28501
       grind)
    | exact superpose eq28501 eq27302
    | exact resolve eq27302 eq28501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28501
  have eq32055 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27302 x X0
       have i₂ := eq31097 X1
       grind)
    | exact superpose eq31097 eq27302
    | (have j1 := eq31097 X1
       grind)
    | exact resolve eq27302 eq31097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31097
  have eq34028 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26263 y X0
       have i₂ := eq32055 X1 X0
       grind)
    | exact superpose eq32055 eq26263
    | (have j1 := eq32055 X1 X1
       grind)
    | exact resolve eq26263 eq32055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26263 eq32055
  have eq72415 : y ≠ y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq34028 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34028
  have eq72416 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq72415
  have eq72426 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72416
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72416
    | exact resolve eq72416 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq72416
  have eq72783 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq72426 eq29
    | exact resolve eq29 eq72426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq72426
  have eq72950 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq72783
    | exact resolve eq72783 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72783
  have eq72951 : y = (M.op x y) := by grind
  clear eq72950
  have eq72952 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq72951 eq20
    | exact resolve eq20 eq72951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq73103 : x = (M.op y x) := by
    first
    | exact superpose eq72951 eq26826
    | exact resolve eq26826 eq72951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26826
  have eq73218 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq72952
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72952
    | exact resolve eq72952 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72952
  have eq73219 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq73218 eq26
    | exact resolve eq26 eq73218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73307 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq73218 eq28420
    | exact resolve eq28420 eq73218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28420
  have eq74043 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq73307
       have i₂ := eq73103
       grind)
    | exact superpose eq73103 eq73307
    | exact resolve eq73307 eq73103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73307
  have eq74060 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq74043 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq74043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74043
  have eq74061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq73219 eq74060
    | exact resolve eq74060 eq73219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74060
  have eq74072 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq74061
       have r₂ := eq27
       grind)
    | exact resolve eq74061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74061
  have eq102136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq74072 eq26131
    | exact resolve eq26131 eq74072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26131 eq74072
  have eq102216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq102136
    | exact resolve eq102136 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq102136
  have eq102218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq73218 eq102216
    | exact resolve eq102216 eq73218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102216
  have eq102219 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq102218
       have r₂ := eq27
       grind)
    | exact resolve eq102218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102218
  have eq102244 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq102219 eq469
    | exact resolve eq469 eq102219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq103297 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq102244 eq27302
    | exact resolve eq27302 eq102244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27302 eq102244
  have eq104997 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq103297 eq102219
    | exact resolve eq102219 eq103297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102219 eq103297
  have eq105087 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq104997
  have eq105113 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq105087 eq28
    | exact resolve eq28 eq105087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq105087
  have eq105376 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq105113
    | exact resolve eq105113 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq105113
  have eq105439 : x = y ∨ x = y := by
    first
    | exact superpose eq72951 eq105376
    | exact resolve eq105376 eq72951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72951 eq105376
  have eq105440 : x = y := by grind
  clear eq105439
  have eq105443 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq105440
       grind)
    | exact superpose eq105440 eq24
    | exact resolve eq24 eq105440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq105607 : x = (M.op x x) := by
    first
    | (have i₁ := eq73103
       have i₂ := eq105440
       grind)
    | exact superpose eq105440 eq73103
    | exact resolve eq73103 eq105440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73103 eq105440
  have eq105817 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq73218 eq105443
    | exact resolve eq105443 eq73218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73218 eq105443
  have eq105928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq105817
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105817
    | exact resolve eq105817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105817
  have eq106098 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105928 eq73219
    | exact resolve eq73219 eq105928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73219
  have eq106326 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4943 x X0
       have i₂ := eq105607
       grind)
    | exact superpose eq105607 eq4943
    | exact resolve eq4943 eq105607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943 eq105607
  have eq108671 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq702 x
       have i₂ := eq106326 x
       grind)
    | exact superpose eq106326 eq702
    | (have j0 := eq702 x
       grind)
    | exact resolve eq702 eq106326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq106326
  have eq108752 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq108671
  have eq108832 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108752
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108752
    | exact resolve eq108752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108752
  have eq108978 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105928 eq108832
    | exact resolve eq108832 eq105928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105928 eq108832
  have eq109120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106098 eq108978
    | exact resolve eq108978 eq106098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106098 eq108978
  have eq109239 : False := by grind
  exact eq109239

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq230 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq344 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq358 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq358
    | exact resolve eq358 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq362 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq364 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq349 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq349
    | exact resolve eq349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq485 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq230
    | exact resolve eq230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq579 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq587 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq589 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq579 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq591 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq589 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq589 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq589 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1181 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq591 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq591
    | (have j0 := eq591 (τ X0) X1
       grind)
    | exact resolve eq591 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1181 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1181
    | (have j0 := eq1181 X0 X1
       grind)
    | exact resolve eq1181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1195 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1189 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1189
    | (have j0 := eq1189 X0 X1
       grind)
    | exact resolve eq1189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1249 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (τ X0) X1
       have i₂ := eq485 X0 X0
       grind)
    | exact superpose eq485 eq1195
    | (have j0 := eq1195 (τ X0) X1
       grind)
    | exact resolve eq1195 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq1195
  have eq3086 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362 eq61
    | exact resolve eq61 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3101 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3086 eq362
    | exact resolve eq362 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq3086
  have eq3119 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3101 eq14
    | exact resolve eq14 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3121 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3119 X0
       have i₂ := eq361 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3119 x
       have i₂ := eq361 (M.op sF4 sF4) x
       grind)
    | exact superpose eq361 eq3119
    | exact resolve eq3119 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3357 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq364 X0 X0 x
       grind)
    | exact superpose eq364 eq61
    | exact resolve eq61 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3393 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq364 X0 X0 X0
       have i₂ := eq3357 X0
       grind)
    | exact superpose eq3357 eq364
    | exact resolve eq364 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3433 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq587 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq587
    | (have j0 := eq587 (τ X0)
       grind)
    | exact resolve eq587 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3444 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3433 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3433
    | (have j0 := eq3433 X0
       grind)
    | exact resolve eq3433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq3451 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3444 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3444
    | (have j0 := eq3444 X0
       grind)
    | exact resolve eq3444 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3814 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq344 X0 X0 x X0 X2
       have i₂ := eq364 X0 X0 x
       grind)
    | exact superpose eq364 eq344
    | exact resolve eq344 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq4933 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3393 X0
       grind)
    | exact superpose eq3393 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3393 X0
       grind)
    | exact resolve eq13 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq4982 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 (M.op X1 X1)
       have i₂ := eq4943 X1 (σ X0)
       grind)
    | exact superpose eq4943 eq330
    | exact resolve eq330 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq4988 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4982 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4982
    | exact resolve eq4982 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq25451 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3121 eq353
    | exact resolve eq353 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq25452 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3121 eq14
    | exact resolve eq14 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq25507 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25452 X0
       have i₂ := eq3393 sF4
       grind)
    | exact superpose eq3393 eq25452
    | exact resolve eq25452 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq25452
  have eq25508 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq25451
       have i₂ := eq3814 sF4 sF4
       grind)
    | exact superpose eq3814 eq25451
    | exact resolve eq25451 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814 eq25451
  have eq25513 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq25508 eq60
    | exact resolve eq60 eq25508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq25508
  have eq25618 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq25507 eq364
    | exact resolve eq364 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq25645 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq25507 eq25618
    | exact resolve eq25618 eq25507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25507 eq25618
  have eq27044 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq25645 X0 X1
       grind)
    | exact superpose eq25645 eq14
    | exact resolve eq14 eq25645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq28510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq28509
    | exact resolve eq28509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28509
  have eq28521 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28510
       have r₂ := eq27
       grind)
    | exact resolve eq28510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28510
  have eq28545 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28521 eq361
    | exact resolve eq361 eq28521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28521
  have eq28602 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28545 eq4943
    | exact resolve eq4943 eq28545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28545
  have eq28671 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq4988 X0 X1
       have i₂ := eq28602 (M.op X1 X1)
       grind)
    | exact superpose eq28602 eq4988
    | (have j1 := eq28602 X1
       grind)
    | exact resolve eq4988 eq28602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988 eq28602
  have eq28717 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq28671
    | (have j0 := eq28671 X0 X1
       grind)
    | exact resolve eq28671 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28671
  have eq28725 : ∀ X0 X1 : G, y = (M.op y x) ∨ (k X1 (σ y)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28717 X0 X1
       have j1 := eq13 X1 (σ y)
       grind)
    | (have r₁ := eq28717 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq28717 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28717
  have eq28748 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X0 (σ y)) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 y x
       have i₂ := eq28725 X0 X1
       grind)
    | exact superpose eq28725 eq361
    | (have j1 := eq28725 X1 X0
       grind)
    | exact resolve eq361 eq28725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq28725
  have eq29112 : ∀ X0 X1 X2 : G, (k X2 x) = X2 ∨ (k X1 (σ y)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4943 y X0
       have i₂ := eq28748 X1 X2
       grind)
    | exact superpose eq28748 eq4943
    | (have j1 := eq28748 X1 X2
       grind)
    | exact resolve eq4943 eq28748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943 eq28748
  have eq29611 : ∀ X0 X1 X2 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq591 x X0
       have i₂ := eq29112 X2 X1 x
       grind)
    | exact superpose eq29112 eq591
    | (have j0 := eq591 x X0
       have j1 := eq29112 X2 X1 X2
       grind)
    | exact resolve eq591 eq29112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq29112
  have eq29637 : ∀ X0 X1 X2 : G, (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq29611 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29611
  have eq29666 : ∀ X0 X1 X2 : G, (k X2 y) = X2 ∨ (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29637 X0 X1 X2
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29637
    | (have j0 := eq29637 X0 X1 X2
       grind)
    | exact resolve eq29637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29637
  have eq31053 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq587 y
       have i₂ := eq29666 X1 X0 y
       grind)
    | exact superpose eq29666 eq587
    | (have j0 := eq587 y
       have j1 := eq29666 X1 X0 x
       grind)
    | exact resolve eq587 eq29666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq29666
  have eq31084 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31053 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31053
  have eq31113 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31084 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31084
    | (have j0 := eq31084 X0 X1
       grind)
    | exact resolve eq31084 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31084
  have eq31173 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31113 X0 X1
       have j1 := eq13 X1 (σ x)
       grind)
    | (have r₁ := eq31113 X0 X1
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq31113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31113
  have eq31244 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X0 X1
       have i₂ := eq31173 (k X0 X0) X1
       grind)
    | exact superpose eq31173 eq1249
    | (have j0 := eq1249 (σ x) X0
       have j1 := eq31173 X1 X1
       grind)
    | exact resolve eq1249 eq31173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31245 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 X0
       have i₂ := eq31173 (k X0 X0) x
       grind)
    | exact superpose eq31173 eq3451
    | (have j0 := eq3451 (σ x)
       have j1 := eq31173 X0 x
       grind)
    | (have r₁ := eq3451 (σ x)
       have r₂ := eq31173 X0 (σ x)
       grind)
    | (have r₁ := eq3451 (σ y)
       have r₂ := eq31173 (σ y) x
       grind)
    | exact resolve eq3451 eq31173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31173
  have eq31278 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq31245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245
  have eq31279 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31244
  have eq31304 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq31279
    | (have j0 := eq31279 X0 X1
       grind)
    | exact resolve eq31279 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq31279
  have eq31365 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25513
       have i₂ := eq31278 (M.op sF2 sF2)
       grind)
    | exact superpose eq31278 eq25513
    | (have j1 := eq31278 X0
       grind)
    | exact resolve eq25513 eq31278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25513 eq31278
  have eq31426 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq31365
    | (have j0 := eq31365 X0
       grind)
    | exact resolve eq31365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31365
  have eq31485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31426 eq3451
    | (have j0 := eq3451 (σ y)
       grind)
    | (have r₁ := eq3451 (σ y)
       have r₂ := eq31426 (σ y)
       grind)
    | exact resolve eq3451 eq31426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31426
  have eq31518 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31485
  have eq31619 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31518 eq27044
    | exact resolve eq27044 eq31518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31518
  have eq31891 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31619 eq25645
    | exact resolve eq25645 eq31619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31619
  have eq32078 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31891 eq26
    | (have j1 := eq31891 (σ x)
       grind)
    | exact resolve eq26 eq31891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31891
  have eq32100 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32078
  have eq32122 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq32100 eq27
    | exact resolve eq27 eq32100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32100
  have eq33358 : ∀ X0 X1 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 X0 X1
       have i₂ := eq31304 (k X0 X0) X1
       grind)
    | exact superpose eq31304 eq1249
    | (have j0 := eq1249 (σ y) X0
       have j1 := eq31304 X1 X1
       grind)
    | exact resolve eq1249 eq31304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq31304
  have eq33393 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33358
  have eq33419 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq33393
    | (have j0 := eq33393 X0 X1
       grind)
    | exact resolve eq33393 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33393
  have eq34001 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 x
       have i₂ := eq33419 X0 x
       grind)
    | exact superpose eq33419 eq3451
    | (have j0 := eq3451 x
       have j1 := eq33419 X0 x
       grind)
    | (have r₁ := eq3451 x
       have r₂ := eq33419 X0 x
       grind)
    | (have r₁ := eq3451 y
       have r₂ := eq33419 y x
       grind)
    | exact resolve eq3451 eq33419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33419
  have eq34034 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq34001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34001
  have eq34877 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27044 x X0
       have i₂ := eq34034 X1
       grind)
    | exact superpose eq34034 eq27044
    | (have j1 := eq34034 X1
       grind)
    | exact resolve eq27044 eq34034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34034
  have eq35747 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 y
       have i₂ := eq34877 X0 y
       grind)
    | exact superpose eq34877 eq3451
    | (have j0 := eq3451 y
       have j1 := eq34877 X0 x
       grind)
    | (have r₁ := eq3451 y
       have r₂ := eq34877 X0 y
       grind)
    | exact resolve eq3451 eq34877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq34877
  have eq35780 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq35747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35747
  have eq36508 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27044 y X0
       have i₂ := eq35780 X1
       grind)
    | exact superpose eq35780 eq27044
    | (have j1 := eq35780 X1
       grind)
    | exact resolve eq27044 eq35780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27044 eq35780
  have eq56768 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25645 y X0
       have i₂ := eq36508 X0 X1
       grind)
    | exact superpose eq36508 eq25645
    | (have j1 := eq36508 X0 X1
       grind)
    | exact resolve eq25645 eq36508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645 eq36508
  have eq58267 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq56768 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56768
  have eq58268 : y = (M.op x y) := by grind
  clear eq58267
  have eq58270 : y = (M.op x y) := by
    first
    | (have i₁ := eq58268
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58268
    | exact resolve eq58268 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58268
  have eq58626 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq58270 eq20
    | exact resolve eq20 eq58270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq58270
  have eq58868 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq58626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58626
    | exact resolve eq58626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq58626
  have eq58870 : False := by grind
  exact eq58870

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq70 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq67 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq180 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq74 X0 X0 x
       grind)
    | exact superpose eq74 eq61
    | exact resolve eq61 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq192 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq74
    | exact resolve eq74 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq180
  have eq209 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq9
    | exact resolve eq9 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq192 X0
       grind)
    | exact resolve eq12 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq213 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq73 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq209 X0 X1
       have i₂ := eq73 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq73 eq209
    | exact resolve eq209 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq260 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq9
    | exact resolve eq9 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq268 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 X1
       have i₂ := eq192 X0
       grind)
    | exact superpose eq192 eq260
    | exact resolve eq260 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq260
  have eq273 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq268 X0 X1
       grind)
    | exact superpose eq268 eq212
    | exact resolve eq212 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq268
  have eq315 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq273 X1 (σ X0)
       grind)
    | exact superpose eq273 eq28
    | exact resolve eq28 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq326 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq315 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq315
    | exact resolve eq315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq521 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq521 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq521
    | (have j0 := eq521 (σ X0) (σ X1)
       grind)
    | exact resolve eq521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq567 X1 X0
       have i₂ := eq521 X1 X0
       grind)
    | exact superpose eq521 eq567
    | (have j0 := eq567 X1 X0
       have j1 := eq521 (σ X1) (σ X0)
       grind)
    | exact resolve eq567 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq27779 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq671 x y
       grind)
    | exact superpose eq671 eq16
    | (have j1 := eq671 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq671 x y
       grind)
    | exact resolve eq16 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq27842 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27779
  have eq27978 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73 (σ x) (σ y)
       have i₂ := eq27842
       grind)
    | exact superpose eq27842 eq73
    | exact resolve eq73 eq27842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27842
  have eq28029 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq326 X0 (σ x)
       have i₂ := eq27978
       grind)
    | exact superpose eq27978 eq326
    | exact resolve eq326 eq27978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq28097 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq28029 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28029
    | exact resolve eq28029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28029
  have eq28114 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x y
       have i₂ := eq28097 X0
       grind)
    | exact superpose eq28097 eq73
    | (have j1 := eq28097 X0
       grind)
    | exact resolve eq73 eq28097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq28097
  have eq28155 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq273 x X1
       have i₂ := eq28114 X0
       grind)
    | exact superpose eq28114 eq273
    | (have j1 := eq28114 X1
       grind)
    | exact resolve eq273 eq28114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq28114
  have eq28558 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28155 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28155
  have eq28559 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28558
  have eq28619 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28559 X0
       have i₂ := eq521 X0 x
       grind)
    | exact superpose eq521 eq28559
    | (have j1 := eq521 X0 x
       grind)
    | exact resolve eq28559 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28714 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq28559 (τ X0)
       grind)
    | exact superpose eq28559 eq17
    | exact resolve eq17 eq28559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28735 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq28714 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28714
    | exact resolve eq28714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28714
  have eq28994 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28735 X0
       have i₂ := eq521 X0 (σ x)
       grind)
    | exact superpose eq521 eq28735
    | (have j1 := eq521 X0 (σ x)
       grind)
    | exact resolve eq28735 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq30694 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq28619 x
       grind)
    | exact superpose eq28619 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq28619 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq28619 x
       grind)
    | exact resolve eq12 eq28619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28619
  have eq30759 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq30694 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30694
  have eq30780 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq30759 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq30759 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq30759 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30759
  have eq30783 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30780 X0
       have i₂ := eq28559 X0
       grind)
    | exact superpose eq28559 eq30780
    | exact resolve eq30780 eq28559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28559 eq30780
  have eq30785 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq27978
       have i₂ := eq30783 y
       grind)
    | exact superpose eq30783 eq27978
    | exact resolve eq27978 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27978
  have eq30787 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30783 y
       grind)
    | exact superpose eq30783 eq16
    | exact resolve eq16 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30783
  have eq32644 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq30785
       grind)
    | exact superpose eq30785 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq30785
       grind)
    | exact resolve eq12 eq30785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30785
  have eq32697 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq32644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32644
  have eq32727 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32697 X0
       have i₂ := eq28735 X0
       grind)
    | exact superpose eq28735 eq32697
    | exact resolve eq32697 eq28735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28735 eq32697
  have eq32736 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30787
       have i₂ := eq32727 (σ y)
       grind)
    | exact superpose eq32727 eq30787
    | (have r₁ := eq30787
       have r₂ := eq32727 (σ y)
       grind)
    | exact resolve eq30787 eq32727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32727
  have eq32817 : x = y := by grind
  clear eq32736
  have eq32919 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30787
       have i₂ := eq32817
       grind)
    | exact superpose eq32817 eq30787
    | exact resolve eq30787 eq32817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30787 eq32817
  have eq35785 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32919
       have i₂ := eq28994 (σ x)
       grind)
    | exact superpose eq28994 eq32919
    | (have j1 := eq28994 (σ x)
       grind)
    | (have r₁ := eq32919
       have r₂ := eq28994 (σ x)
       grind)
    | exact resolve eq32919 eq28994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28994
  have eq35871 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq35785
  have eq35914 : False := by grind
  exact eq35914

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_pyy_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq18
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq72 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq69 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq75
    | exact resolve eq75 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq75 X0 X0 x
       grind)
    | exact superpose eq75 eq52
    | exact resolve eq52 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq193 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq193
    | exact resolve eq193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq225 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq84 X0 X0
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq84 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq84 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq237 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq239 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq237 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq237 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq237 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq248 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0 X0 X0
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq75
    | exact resolve eq75 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq200 X0
       grind)
    | exact superpose eq200 eq52
    | exact resolve eq52 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq200
  have eq266 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq9
    | exact resolve eq9 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq248 X0
       grind)
    | exact resolve eq12 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq271 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq74 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq266 X0 X1
       have i₂ := eq74 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq74 eq266
    | exact resolve eq266 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq552 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq271 X0 X1
       grind)
    | exact superpose eq271 eq9
    | exact resolve eq9 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq552
    | exact resolve eq552 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq571 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X1 X0
       have i₂ := eq560 X1 X0
       grind)
    | exact superpose eq560 eq271
    | exact resolve eq271 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq574 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq560 X1 X0
       grind)
    | exact superpose eq560 eq9
    | exact resolve eq9 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq239 (M.op X0 X0) X1
       have i₂ := eq269 X0 (M.op X0 X0)
       grind)
    | exact superpose eq269 eq239
    | (have j0 := eq239 (M.op X0 X0) X1
       grind)
    | exact resolve eq239 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq661 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq641 X0 X1
       have i₂ := eq248 X0
       grind)
    | exact superpose eq248 eq641
    | (have j0 := eq641 X0 X1
       grind)
    | exact resolve eq641 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq641
  have eq662 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq950 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq560 X0 X2
       have i₂ := eq662 X1 X0
       grind)
    | exact superpose eq662 eq560
    | exact resolve eq560 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X1)
       have i₂ := eq662 X1 X0
       grind)
    | exact superpose eq662 eq23
    | exact resolve eq23 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq662
  have eq1022 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq950 (σ X0) X1 X2
       have i₂ := eq15 X0 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq950
    | exact resolve eq950 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1085 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1022 X0 x X2
       have i₂ := eq269 x X0
       grind)
    | exact superpose eq269 eq1022
    | exact resolve eq1022 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1172 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 (σ (M.op X1 X1))
       have i₂ := eq1085 X1 X0
       grind)
    | exact superpose eq1085 eq574
    | exact resolve eq574 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq965 X0 x
       have i₂ := eq269 x (τ X0)
       grind)
    | exact superpose eq269 eq965
    | exact resolve eq965 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq965
  have eq2224 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1653 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1653
    | exact resolve eq1653 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq2810 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2224 X0
       grind)
    | exact superpose eq2224 eq11
    | exact resolve eq11 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq3104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq225
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq225
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq225 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq3105 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq3104
  have eq38130 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq210 X0 X0 X1 X2
       grind)
    | exact superpose eq210 eq9
    | exact resolve eq9 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq38194 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38130 X0 X1 X2
       have i₂ := eq560 X0 X1
       grind)
    | exact superpose eq560 eq38130
    | exact resolve eq38130 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38130
  have eq38524 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38194 (M.op (M.op X0 X0) (M.op X0 X1)) X2 X0
       have i₂ := eq249 X0 X1
       grind)
    | exact superpose eq249 eq38194
    | exact resolve eq38194 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq38194
  have eq38737 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38524 X0 X1 X2
       have i₂ := eq560 X0 (M.op X0 X1)
       grind)
    | exact superpose eq560 eq38524
    | exact resolve eq38524 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq38524
  have eq49242 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3105
       have i₂ := eq2810 y
       grind)
    | exact superpose eq2810 eq3105
    | exact resolve eq3105 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq49243 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49242
       have i₂ := eq2810 y
       grind)
    | exact superpose eq2810 eq49242
    | exact resolve eq49242 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810 eq49242
  have eq50865 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq49243
       grind)
    | exact superpose eq49243 eq10
    | exact resolve eq10 eq49243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49243
  have eq50960 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq50865
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50865
    | exact resolve eq50865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50865
  have eq50961 : (σ x) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq50960
  have eq779167 : (M.op y y) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq50961
       grind)
    | exact superpose eq50961 eq10
    | exact resolve eq10 eq50961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50961
  have eq779615 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq779167
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq779167
    | exact resolve eq779167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779167
  have eq779616 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq779615
  have eq780368 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38737 y y X0
       have i₂ := eq779616
       grind)
    | exact superpose eq779616 eq38737
    | exact resolve eq38737 eq779616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38737 eq779616
  have eq780385 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq780368 X0
       have i₂ := eq574 X0 y
       grind)
    | exact superpose eq574 eq780368
    | exact resolve eq780368 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780368
  have eq780754 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 y X0
       have i₂ := eq780385 X1
       grind)
    | exact superpose eq780385 eq1085
    | (have j1 := eq780385 X1
       grind)
    | exact resolve eq1085 eq780385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq781037 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq74 y y
       have i₂ := eq780385 X0
       grind)
    | exact superpose eq780385 eq74
    | (have j1 := eq780385 x
       grind)
    | exact resolve eq74 eq780385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq780385
  have eq783673 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq781037 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781037
  have eq783674 : x = (M.op y x) := by grind
  clear eq783673
  have eq783709 : y = (M.op x y) := by
    first
    | (have i₁ := eq574 x y
       have i₂ := eq783674
       grind)
    | exact superpose eq783674 eq574
    | exact resolve eq574 eq783674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq783674
  have eq797596 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq780754 (σ y) X0
       grind)
    | exact superpose eq780754 eq16
    | (have j1 := eq780754 X0 X0
       grind)
    | exact resolve eq16 eq780754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780754
  have eq798807 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq797596 X0
       have i₂ := eq783709
       grind)
    | exact superpose eq783709 eq797596
    | (have j0 := eq797596 X0
       grind)
    | exact resolve eq797596 eq783709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783709 eq797596
  have eq798808 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq798807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798807
  have eq798876 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq571 X0 y
       have i₂ := eq798808 y
       grind)
    | exact superpose eq798808 eq571
    | exact resolve eq571 eq798808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq798915 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1172 X0 y
       have i₂ := eq798808 y
       grind)
    | exact superpose eq798808 eq1172
    | exact resolve eq1172 eq798808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq798808
  have eq816383 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq798915 (σ x)
       grind)
    | exact superpose eq798915 eq16
    | exact resolve eq16 eq798915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798915
  have eq816784 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq816383
       have i₂ := eq798876 x
       grind)
    | exact superpose eq798876 eq816383
    | exact resolve eq816383 eq798876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798876 eq816383
  have eq816785 : False := by grind
  exact eq816785

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxx_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq74
    | (have j1 := eq68 x x
       grind)
    | exact resolve eq74 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq68
    | (have j0 := eq68 x (σ x)
       grind)
    | exact resolve eq68 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq649
    | exact resolve eq649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq653 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq650
       have r₂ := eq27
       grind)
    | exact resolve eq650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq653 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq653
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq653
       grind)
    | exact resolve eq13 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq661 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq656
  have eq683 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq661 eq49
    | exact resolve eq49 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq661
  have eq687 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq683
    | exact resolve eq683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq683
  have eq690 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68 x x
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq68
    | (have j0 := eq68 x x
       grind)
    | exact resolve eq68 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq691 : x = (M.op x x) := by grind
  clear eq690
  have eq752 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq691
       grind)
    | exact resolve eq13 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq52
    | exact resolve eq52 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : x = (k x x) := by grind
  clear eq752
  have eq758 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq754
    | exact resolve eq754 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq754
  have eq768 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq43
    | exact resolve eq43 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq757
  have eq772 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq768
    | exact resolve eq768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq768
  have eq836 : y = (M.op x y) := by
    first
    | (have i₁ := eq758 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq758
    | (have j0 := eq758 y
       grind)
    | exact resolve eq758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq758
  have eq857 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq836 eq20
    | exact resolve eq20 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq836
  have eq876 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq857
    | exact resolve eq857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq857
  have eq878 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq876 eq26
    | exact resolve eq26 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq876
  have eq899 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq772 eq68
    | (have j0 := eq68 x (σ x)
       grind)
    | exact resolve eq68 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq772
  have eq900 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq899
  have eq933 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq900 eq52
    | exact resolve eq52 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq937 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq900 eq933
    | exact resolve eq933 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq933
  have eq959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq937 eq878
    | exact resolve eq878 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq937
  have eq981 : False := by grind
  exact eq981
