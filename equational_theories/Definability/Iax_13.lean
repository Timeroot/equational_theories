import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1253`: `x = x ◇ (((y ◇ y) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation1253 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1253 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1253.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op (M.op X0 X0) X0) X1)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op (M.op X0 X0) X0) X1) X3
       have i₂ := eq8 (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op (M.op X0 X0) X0) X1)) X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq8 (M.op (M.op X0 X0) X0) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op (M.op X0 X0) X0) X1) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X0 X1 X2 X3
       have i₂ := eq8 (M.op (M.op (M.op X0 X0) X0) X1) X0 X1
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) ≠ (M.op (M.op (M.op X0 X0) X0) X1) ∨ (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op (M.op X0 X0) X0) X1)
       have i₂ := eq8 (M.op (M.op (M.op X0 X0) X0) X1) X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X2 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op (M.op X1 X1) X1) X2)
       have r₂ := eq8 (M.op (M.op (M.op X1 X1) X1) X2) X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = X1 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq137 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (k (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op (M.op X2 X2) X2) X3))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X0 X1 X4 (M.op (M.op (M.op X0 X0) X0) X1)
       have i₂ := eq36 X2 X3 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq36 eq24
    | exact resolve eq24 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq193 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq53 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq53 eq13
    | (have j1 := eq53 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq53 X1 X2 (τ X0)
       grind)
    | exact superpose eq53 eq15
    | (have j1 := eq53 X1 X2 X2
       grind)
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq237 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq35 X1 (τ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X2)) = X1 ∨ (k X3 X0) = (M.op X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq48 X0 X1 X2 X3
       have i₂ := eq12 X4 X0
       grind)
    | exact superpose eq12 eq48
    | (have j0 := eq48 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (k (M.op X0 X0) (M.op (M.op (M.op X1 X1) X1) X2))) = X3 ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq48 X0 X3 (M.op X0 X0) X4
       have i₂ := eq36 X1 X2 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq48
    | (have j0 := eq48 X0 X1 X2 X4
       grind)
    | exact resolve eq48 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq48
  have eq469 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) ≠ (k X0 (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X1 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq200
    | exact resolve eq200 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq475 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq469 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq488 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq475 (σ X0)
       grind)
    | exact superpose eq475 eq13
    | exact resolve eq13 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq488 X0
       have i₂ := eq475 X0
       grind)
    | exact superpose eq475 eq488
    | exact resolve eq488 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq631 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq23
    | exact resolve eq23 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op (M.op X1 X1) X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq480 (σ X0) X1
       grind)
    | (have i₁ := eq42 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq480 (σ X0) X1
       grind)
    | exact superpose eq480 eq42
    | exact resolve eq42 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq753 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq748
    | exact resolve eq748 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq779 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq42 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq42 eq753
    | exact resolve eq753 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1083 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1083
    | (have j0 := eq1083 X0 X1
       grind)
    | exact resolve eq1083 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1178 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq23 eq631
    | exact resolve eq631 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1265 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1178 X0 X1
       have i₂ := eq500 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq500 eq1178
    | exact resolve eq1178 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1277 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1265 X0 X1
       have i₂ := eq23 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq23 eq1265
    | exact resolve eq1265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1487 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ (M.op (M.op X0 X0) X0))
       have i₂ := eq1277 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq1277 eq11
    | (have j0 := eq11 X1 (σ (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq11 X0 (σ (M.op (M.op X0 X0) X0))
       have r₂ := eq1277 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq11 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq2566 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X0
       have i₂ := eq779 (τ X0) X1
       grind)
    | (have i₁ := eq54 (M.op (M.op X1 X1) X1) X1
       have i₂ := eq779 (τ X1) X1
       grind)
    | exact superpose eq779 eq54
    | exact resolve eq54 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq2586 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2566 X0 X1
       have i₂ := eq54 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq54 eq2566
    | exact resolve eq2566 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2566
  have eq2638 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2586 X0 X1
       have i₂ := eq475 X0
       grind)
    | exact superpose eq475 eq2586
    | exact resolve eq2586 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq2586
  have eq6044 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq195
    | (have j0 := eq195 X0 X1 X2
       grind)
    | exact resolve eq195 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq6344 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6044 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6044
    | (have j0 := eq6044 X0 X1 X2
       grind)
    | exact resolve eq6044 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6044
  have eq13075 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X0 (σ X1)
       have i₂ := eq193 X2 X1 (σ X0)
       grind)
    | exact superpose eq193 eq42
    | (have j1 := eq193 X2 X1 X2
       grind)
    | exact resolve eq42 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq193
  have eq13082 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13075 X0 X1 X2
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq13075
    | (have j0 := eq13075 X0 X1 X2
       grind)
    | exact resolve eq13075 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13075
  have eq13222 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13082 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq13082
    | (have j0 := eq13082 X0 X1 X2
       grind)
    | exact resolve eq13082 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq13257 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13222 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq13222
    | (have j0 := eq13222 X0 X1 X2
       grind)
    | exact resolve eq13222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13222
  have eq39611 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X1 X3)) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq247 X1 X2 X3 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq39612 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq39611 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39611
  have eq50822 : ∀ X0 X1 X6 : G, (M.op X1 X0) = X1 ∨ (k X6 X0) = (M.op X6 X0) := by
    intro X0 X1 X6
    first
    | (have i₁ := eq39612 X6 X0 X1 (k (M.op (M.op (M.op x x) x) x) (M.op (M.op (M.op x x) x) x))
       have i₂ := eq137 x x x x X0
       grind)
    | exact superpose eq137 eq39612
    | (have j0 := eq39612 X6 X0 x x
       grind)
    | exact resolve eq39612 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq50824 : ∀ X0 X1 X2 X5 X6 : G, (M.op X1 X0) = X1 ∨ (k X5 X0) = (M.op X5 X0) ∨ (k X6 X2) = (M.op X6 X2) := by
    intro X0 X1 X2 X5 X6
    first
    | (have i₁ := eq39612 X5 X0 X1 (k (M.op X2 X2) (M.op (M.op (M.op x x) x) x))
       have i₂ := eq254 X2 x x X0 X6
       grind)
    | exact superpose eq254 eq39612
    | (have j0 := eq39612 X5 X0 X2 x
       have j1 := eq254 X0 X1 X2 x X5
       grind)
    | exact resolve eq39612 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq39612
  have eq52311 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq50822 X0 X0 X2
       grind)
    | exact superpose eq50822 eq200
    | (have j0 := eq200 X0 X1
       have j1 := eq50822 X1 X1 X0
       grind)
    | exact resolve eq200 eq50822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq50822
  have eq52715 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52311 X0 X1 X2
       have j1 := eq50824 X1 X1 X1 X0 X0
       grind)
    | (have r₁ := eq52311 X1 X0 X2
       have r₂ := eq50824 X0 X1 X2 x x
       grind)
    | exact resolve eq52311 eq50824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50824 eq52311
  have eq75081 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X0 (M.op (M.op X1 X1) X1))) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2638 X0 X1
       have i₂ := eq52715 X0 (M.op (M.op X1 X1) X1) X2
       grind)
    | exact superpose eq52715 eq2638
    | (have j1 := eq52715 X2 X0 X2
       grind)
    | exact resolve eq2638 eq52715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq52715
  have eq75376 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq75081 X0 x X2
       have i₂ := eq23 x X0
       grind)
    | exact superpose eq23 eq75081
    | (have j0 := eq75081 X0 x X2
       grind)
    | exact resolve eq75081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75081
  have eq88765 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75376 (σ X0) X1
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq75376
    | (have j0 := eq75376 (σ X0) X1
       grind)
    | exact resolve eq75376 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75376
  have eq89144 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88765 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq88765
    | (have j0 := eq88765 X0 X1
       grind)
    | exact resolve eq88765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88765
  have eq89215 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89144 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq89144
    | (have j0 := eq89144 X0 X1
       grind)
    | exact resolve eq89144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89144
  have eq157045 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq13257 X0 y x
       grind)
    | exact superpose eq13257 eq14
    | (have j1 := eq13257 X0 y x
       grind)
    | exact resolve eq14 eq13257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13257
  have eq157056 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq157045 X0
       have j1 := eq6344 X0 y X0
       grind)
    | (have r₁ := eq157045 X0
       have r₂ := eq6344 x y x
       grind)
    | exact resolve eq157045 eq6344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6344 eq157045
  have eq157302 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X1 X0
       have i₂ := eq157056 X0
       grind)
    | exact superpose eq157056 eq1529
    | exact resolve eq1529 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq157532 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq500 X0
       have i₂ := eq157056 (σ X0)
       grind)
    | exact superpose eq157056 eq500
    | exact resolve eq500 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq157554 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (σ (k (τ X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq157056 (τ X0)
       grind)
    | exact superpose eq157056 eq237
    | exact resolve eq237 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq157599 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1169 X0 y
       have i₂ := eq157056 X0
       grind)
    | exact superpose eq157056 eq1169
    | (have j0 := eq1169 X0 y
       grind)
    | exact resolve eq1169 eq157056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq157056
  have eq157627 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq157554 X0 X1
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq157554
    | exact resolve eq157554 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq157554
  have eq157743 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq157627 X0 x
       have i₂ := eq157302 X0 x
       grind)
    | exact superpose eq157302 eq157627
    | exact resolve eq157627 eq157302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157302 eq157627
  have eq158162 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq89215 y X0
       have i₂ := eq157743 X0
       grind)
    | exact superpose eq157743 eq89215
    | (have j0 := eq89215 y x
       grind)
    | exact resolve eq89215 eq157743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89215 eq157743
  have eq200000 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158162 (σ x)
       grind)
    | exact superpose eq158162 eq14
    | exact resolve eq14 eq158162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158162
  have eq200066 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq200000
       have i₂ := eq157532 x
       grind)
    | exact superpose eq157532 eq200000
    | exact resolve eq200000 eq157532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157532 eq200000
  have eq200151 : y = (M.op y y) := by
    first
    | (have r₁ := eq200066
       have r₂ := eq157599 x
       grind)
    | exact resolve eq200066 eq157599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157599 eq200066
  have eq200193 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq200151
       grind)
    | exact superpose eq200151 eq23
    | exact resolve eq23 eq200151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq200311 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1277 y X0
       have i₂ := eq200151
       grind)
    | exact superpose eq200151 eq1277
    | exact resolve eq1277 eq200151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq200604 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq200311 X0
       have i₂ := eq200151
       grind)
    | exact superpose eq200151 eq200311
    | exact resolve eq200311 eq200151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200311
  have eq200707 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq200193 X0
       have i₂ := eq200151
       grind)
    | exact superpose eq200151 eq200193
    | exact resolve eq200193 eq200151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200151 eq200193
  have eq202842 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200604 (σ x)
       grind)
    | exact superpose eq200604 eq14
    | exact resolve eq14 eq200604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200604
  have eq203031 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq202842
       have i₂ := eq200707 x
       grind)
    | exact superpose eq200707 eq202842
    | exact resolve eq202842 eq200707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200707 eq202842
  have eq203032 : False := by grind
  exact eq203032

/-- `Equation1254`: `x = x ◇ (((y ◇ y) ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1254 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1254 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1254.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1078 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq113 x y
       grind)
    | exact superpose eq113 eq14
    | (have r₁ := eq14
       have r₂ := eq113 x y
       grind)
    | exact resolve eq14 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1099 : False := by grind
  exact eq1099

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation1255 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq22 X0 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X0) X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq32
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) ≠ (M.op (M.op (M.op X0 X0) X1) X0) ∨ (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op (M.op X0 X0) X1) X0)
       have i₂ := eq8 (M.op (M.op (M.op X0 X0) X1) X0) X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X2 (M.op (M.op (M.op X0 X0) X1) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op (M.op X1 X1) X2) X1)
       have r₂ := eq8 (M.op (M.op (M.op X1 X1) X2) X1) X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq128 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq22 X0 (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1)
       grind)
    | exact superpose eq22 eq40
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq146 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq128
    | exact resolve eq128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq198 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq57 eq13
    | (have j1 := eq57 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq57 X1 X2 (τ X0)
       grind)
    | exact superpose eq57 eq15
    | (have j1 := eq57 X1 X2 X2
       grind)
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq326 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) X1)) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op (M.op (M.op X1 X1) X1) X2)
       have i₂ := eq146 X1 X2 (τ X0)
       grind)
    | exact superpose eq146 eq15
    | exact resolve eq15 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq751 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) ≠ (k X0 (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X1 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq205
    | exact resolve eq205 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq757 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq205 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq762 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq751 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq816 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq757 (σ X0)
       grind)
    | exact superpose eq757 eq13
    | exact resolve eq13 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq816 X0
       have i₂ := eq757 X0
       grind)
    | exact superpose eq757 eq816
    | exact resolve eq816 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq962 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq22
    | exact resolve eq22 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op (M.op X1 X1) X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq762 (σ X0) X1
       grind)
    | (have i₁ := eq46 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq762 (σ X0) X1
       grind)
    | exact superpose eq762 eq46
    | exact resolve eq46 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1107 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1102 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1102
    | exact resolve eq1102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1139 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X0 X1
       have i₂ := eq46 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq46 eq1107
    | exact resolve eq1107 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1324 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1420 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1324 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1324
    | (have j0 := eq1324 X0 X1
       grind)
    | exact resolve eq1324 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1730 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq962 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq962
    | exact resolve eq962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op (M.op X0 X0) X0) X1)) (σ (M.op (M.op (M.op X0 X0) X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq962 (M.op (M.op (M.op X0 X0) X0) X1) X2
       have i₂ := eq33 X0 X1 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq33 eq962
    | exact resolve eq962 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1843 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op (M.op X0 X0) X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1734 X0 X1 X2
       have i₂ := eq828 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq828 eq1734
    | exact resolve eq1734 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1847 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1
       have i₂ := eq828 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq828 eq1730
    | exact resolve eq1730 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1858 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1843 X0 X1 X2
       have i₂ := eq33 X0 X1 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq33 eq1843
    | exact resolve eq1843 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1843
  have eq1861 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1847 X0 X1
       have i₂ := eq22 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq1847
    | exact resolve eq1847 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq3314 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X0
       have i₂ := eq1139 (τ X0) X1
       grind)
    | (have i₁ := eq58 (M.op (M.op X1 X1) X1) X1
       have i₂ := eq1139 (τ X1) X1
       grind)
    | exact superpose eq1139 eq58
    | exact resolve eq58 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq3337 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3314 X0 X1
       have i₂ := eq58 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq58 eq3314
    | exact resolve eq3314 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq3314
  have eq3395 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3337 X0 X1
       have i₂ := eq757 X0
       grind)
    | exact superpose eq757 eq3337
    | exact resolve eq3337 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq3337
  have eq6535 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq200
    | (have j0 := eq200 X0 X1 X2
       grind)
    | exact resolve eq200 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq6841 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6535 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6535
    | (have j0 := eq6535 X0 X1 X2
       grind)
    | exact resolve eq6535 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6974 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X0) X0) X1)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) X1)) ∨ (M.op X2 X2) = (k X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       have i₂ := eq1858 X0 X1 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | exact superpose eq1858 eq11
    | (have j0 := eq11 X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | (have r₁ := eq11 X0 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       have r₂ := eq1858 X0 X1 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | exact resolve eq11 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858
  have eq7084 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6974 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq13932 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 X0 (σ X1)
       have i₂ := eq198 X2 X1 (σ X0)
       grind)
    | exact superpose eq198 eq46
    | (have j1 := eq198 X2 X1 X2
       grind)
    | exact resolve eq46 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq198
  have eq13939 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13932 X0 X1 X2
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq13932
    | (have j0 := eq13932 X0 X1 X2
       grind)
    | exact resolve eq13932 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq14077 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13939 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq13939
    | (have j0 := eq13939 X0 X1 X2
       grind)
    | exact resolve eq13939 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq14108 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14077 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq14077
    | (have j0 := eq14077 X0 X1 X2
       grind)
    | exact resolve eq14077 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077
  have eq113127 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3395 X0 x
       have i₂ := eq326 X0 x X2
       grind)
    | exact superpose eq326 eq3395
    | (have j1 := eq326 X0 x X2
       grind)
    | exact resolve eq3395 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq3395
  have eq113138 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113127 (σ X0) X1
       have i₂ := eq828 X0
       grind)
    | exact superpose eq828 eq113127
    | (have j0 := eq113127 (σ X0) X1
       grind)
    | exact resolve eq113127 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113127
  have eq113167 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113138 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq113138
    | (have j0 := eq113138 X0 X1
       grind)
    | exact resolve eq113138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113138
  have eq113172 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113167 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq113167
    | (have j0 := eq113167 X0 X1
       grind)
    | exact resolve eq113167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113167
  have eq127033 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq14108 X0 y x
       grind)
    | exact superpose eq14108 eq14
    | (have j1 := eq14108 X0 y x
       grind)
    | exact resolve eq14 eq14108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14108
  have eq127037 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq127033 X0
       have j1 := eq6841 X0 y X0
       grind)
    | (have r₁ := eq127033 X0
       have r₂ := eq6841 x y x
       grind)
    | exact resolve eq127033 eq6841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841 eq127033
  have eq127381 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (k X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7084 X1 X2 X0
       have i₂ := eq127037 X0
       grind)
    | exact superpose eq127037 eq7084
    | exact resolve eq7084 eq127037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7084
  have eq127557 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq828 X0
       have i₂ := eq127037 (σ X0)
       grind)
    | exact superpose eq127037 eq828
    | exact resolve eq828 eq127037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq127581 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (σ (k (τ X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X0 X1 X2
       have i₂ := eq127037 (τ X0)
       grind)
    | exact superpose eq127037 eq554
    | exact resolve eq554 eq127037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq127628 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1420 X0 y
       have i₂ := eq127037 X0
       grind)
    | exact superpose eq127037 eq1420
    | (have j0 := eq1420 X0 y
       grind)
    | exact resolve eq1420 eq127037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq127037
  have eq127646 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (k X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127581 X0 X1 X2
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq127581
    | exact resolve eq127581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq127581
  have eq127702 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq127646 X0 x x
       have i₂ := eq127381 X0 x x
       grind)
    | exact superpose eq127381 eq127646
    | exact resolve eq127646 eq127381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127381 eq127646
  have eq128081 : ∀ X0 : G, (k X0 y) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq113172 y X0
       have i₂ := eq127702 X0
       grind)
    | exact superpose eq127702 eq113172
    | (have j0 := eq113172 y x
       grind)
    | exact resolve eq113172 eq127702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113172 eq127702
  have eq198198 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq128081 (σ x)
       grind)
    | exact superpose eq128081 eq14
    | exact resolve eq14 eq128081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128081
  have eq198229 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq198198
       have i₂ := eq127557 x
       grind)
    | exact superpose eq127557 eq198198
    | exact resolve eq198198 eq127557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127557 eq198198
  have eq198269 : y = (M.op y y) := by
    first
    | (have r₁ := eq198229
       have r₂ := eq127628 x
       grind)
    | exact resolve eq198229 eq127628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127628 eq198229
  have eq198405 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq198269
       grind)
    | exact superpose eq198269 eq22
    | exact resolve eq22 eq198269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq198585 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1861 y X0
       have i₂ := eq198269
       grind)
    | exact superpose eq198269 eq1861
    | exact resolve eq1861 eq198269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq198890 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq198585 X0
       have i₂ := eq198269
       grind)
    | exact superpose eq198269 eq198585
    | exact resolve eq198585 eq198269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198585
  have eq199026 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq198405 X0
       have i₂ := eq198269
       grind)
    | exact superpose eq198269 eq198405
    | exact resolve eq198405 eq198269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198269 eq198405
  have eq201883 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq198890 (σ x)
       grind)
    | exact superpose eq198890 eq14
    | exact resolve eq14 eq198890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198890
  have eq202123 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq201883
       have i₂ := eq199026 x
       grind)
    | exact superpose eq199026 eq201883
    | exact resolve eq201883 eq199026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199026 eq201883
  have eq202124 : False := by grind
  exact eq202124

/-- `Equation1256`: `x = x ◇ (((y ◇ y) ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1256 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1256 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1256.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op (M.op X1 X1) X2) X2)
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) X2) X2)) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq23 X0 x x X3
       have i₂ := eq8 (M.op X0 X0) x x
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq57
    | exact resolve eq57 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq254 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq47 X2 X0
       grind)
    | exact superpose eq47 eq24
    | (have j1 := eq47 X2 X0
       grind)
    | exact resolve eq24 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq47 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq599 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq1456 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq259 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq259
    | (have j0 := eq259 (M.op X0 X0)
       grind)
    | exact resolve eq259 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1471 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq259 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq259
    | (have j0 := eq259 (τ X0)
       grind)
    | exact resolve eq259 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq259
  have eq1483 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1488 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1471
    | (have j0 := eq1471 X0
       grind)
    | exact resolve eq1471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1497 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1488 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1488
    | (have j0 := eq1488 X0
       grind)
    | exact resolve eq1488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1679 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1483 X0
       grind)
    | exact superpose eq1483 eq24
    | exact resolve eq24 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq1765 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1679 X0 X1
       have i₂ := eq650 X2 X0
       grind)
    | exact superpose eq650 eq1679
    | (have j1 := eq650 X2 X0
       grind)
    | exact resolve eq1679 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq1679
  have eq1883 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq254 y X0 x
       grind)
    | exact superpose eq254 eq14
    | (have j1 := eq254 y X0 x
       grind)
    | exact resolve eq14 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1911 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1883 X0
       have j1 := eq1765 y X0 x
       grind)
    | (have r₁ := eq1883 X0
       have r₂ := eq1765 y x x
       grind)
    | exact resolve eq1883 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765 eq1883
  have eq1926 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq131 (σ y) x
       have i₂ := eq1911 (σ y)
       grind)
    | exact superpose eq1911 eq131
    | exact resolve eq131 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1942 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1911 (σ x)
       grind)
    | exact superpose eq1911 eq14
    | exact resolve eq14 eq1911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1960 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1926 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1926
    | exact resolve eq1926 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq2088 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1497 y
       have i₂ := eq1960 y
       grind)
    | exact superpose eq1960 eq1497
    | (have j0 := eq1497 y
       grind)
    | (have r₁ := eq1497 y
       have r₂ := eq1960 y
       grind)
    | exact resolve eq1497 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq1960
  have eq2104 : y = (M.op y y) := by grind
  clear eq2088
  have eq2219 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq2104
       grind)
    | exact superpose eq2104 eq24
    | exact resolve eq24 eq2104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2104
  have eq2740 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1942
       have i₂ := eq2219 x
       grind)
    | exact superpose eq2219 eq1942
    | exact resolve eq1942 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq2219
  have eq2741 : False := by grind
  exact eq2741

/-- `Equation1259`: `x = x ◇ (((y ◇ z) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1259 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1259 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1259.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq84 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq88 (σ X0) (σ X1)
       grind)
    | exact superpose eq88 eq13
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq104
    | exact resolve eq104 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq104
  have eq1323 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109 x y
       grind)
    | exact superpose eq109 eq14
    | (have r₁ := eq14
       have r₂ := eq109 x y
       grind)
    | exact resolve eq14 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1345 : False := by grind
  exact eq1345

/-- `Equation1263`: `x = x ◇ (((y ◇ z) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation1263 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1263 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1263.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq21 X0 (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X0) X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq21 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq21 eq32
    | exact resolve eq32 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X0) ≠ (M.op (M.op (M.op X0 X1) X0) X0) ∨ (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X1) X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op (M.op X0 X1) X0) X0)
       have i₂ := eq8 (M.op (M.op (M.op X0 X1) X0) X0) X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X2 (M.op (M.op (M.op X0 X1) X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op (M.op X1 X2) X1) X1)
       have r₂ := eq8 (M.op (M.op (M.op X1 X2) X1) X1) X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq21 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq21 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X1) X0) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq124 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq21 X0 (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq21 eq40
    | exact resolve eq40 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq140 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op (M.op X0 X0) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X0 X1 X2
       have i₂ := eq21 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq21 eq124
    | exact resolve eq124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq189 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq56 eq13
    | (have j1 := eq56 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq56 X1 X2 (τ X0)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 X1 X2 X2
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq316 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X1) X1)) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op (M.op (M.op X1 X1) X1) X2)
       have i₂ := eq140 X1 X2 (τ X0)
       grind)
    | exact superpose eq140 eq15
    | exact resolve eq15 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq656 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) ≠ (k X0 (M.op (M.op X1 X1) X1)) ∨ (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X1 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq196
    | exact resolve eq196 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq662 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq196 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq667 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq656 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq676 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq662 (σ X0)
       grind)
    | exact superpose eq662 eq13
    | exact resolve eq13 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq676 X0
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq676
    | exact resolve eq676 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq829 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq688 X0
       grind)
    | exact superpose eq688 eq21
    | exact resolve eq21 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op (M.op X1 X1) X1))) = (k X0 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq667 (σ X0) X1
       grind)
    | (have i₁ := eq46 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq667 (σ X0) X1
       grind)
    | exact superpose eq667 eq46
    | exact resolve eq46 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq947 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq942
    | exact resolve eq942 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq975 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq46 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq46 eq947
    | exact resolve eq947 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1316 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1316
    | (have j0 := eq1316 X0 X1
       grind)
    | exact resolve eq1316 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1420 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq829 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq21 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq21 eq829
    | exact resolve eq829 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op (M.op X0 X0) X0) X1)) (σ (M.op (M.op (M.op X0 X0) X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq829 (M.op (M.op (M.op X0 X0) X0) X1) X2
       have i₂ := eq33 X0 X1 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq33 eq829
    | exact resolve eq829 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq1522 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op (M.op (M.op X0 X0) X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1422 X0 X1 X2
       have i₂ := eq688 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq688 eq1422
    | exact resolve eq1422 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1524 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1420 X0 X1
       have i₂ := eq688 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq688 eq1420
    | exact resolve eq1420 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1536 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1522 X0 X1 X2
       have i₂ := eq33 X0 X1 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq33 eq1522
    | exact resolve eq1522 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1522
  have eq1538 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1524 X0 X1
       have i₂ := eq21 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq21 eq1524
    | exact resolve eq1524 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq2944 : ∀ X0 X1 : G, (τ (k X0 X0)) = (k (τ X0) (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X0
       have i₂ := eq975 (τ X0) X1
       grind)
    | (have i₁ := eq57 (M.op (M.op X1 X1) X1) X1
       have i₂ := eq975 (τ X1) X1
       grind)
    | exact superpose eq975 eq57
    | exact resolve eq57 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq2963 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2944 X0 X1
       have i₂ := eq57 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq57 eq2944
    | exact resolve eq2944 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2944
  have eq3017 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2963 X0 X1
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq2963
    | exact resolve eq2963 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq2963
  have eq5770 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq191
    | (have j0 := eq191 X0 X1 X2
       grind)
    | exact resolve eq191 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq6050 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5770 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5770
    | (have j0 := eq5770 X0 X1 X2
       grind)
    | exact resolve eq5770 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq6175 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X0) X0) X1)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) X1)) ∨ (M.op X2 X2) = (k X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       have i₂ := eq1536 X0 X1 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | exact superpose eq1536 eq11
    | (have j0 := eq11 X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | (have r₁ := eq11 X0 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       have r₂ := eq1536 X0 X1 (σ (M.op (M.op (M.op X0 X0) X0) X1))
       grind)
    | exact resolve eq11 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq6279 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op (M.op (M.op X0 X0) X0) X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6175 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6175
  have eq10446 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 X0 (σ X1)
       have i₂ := eq189 X2 X1 (σ X0)
       grind)
    | exact superpose eq189 eq46
    | (have j1 := eq189 X2 X1 X2
       grind)
    | exact resolve eq46 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq189
  have eq10453 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10446 X0 X1 X2
       have i₂ := eq688 X0
       grind)
    | exact superpose eq688 eq10446
    | (have j0 := eq10446 X0 X1 X2
       grind)
    | exact resolve eq10446 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10446
  have eq10565 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10453 X0 X1 X2
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10453
    | (have j0 := eq10453 X0 X1 X2
       grind)
    | exact resolve eq10453 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq10594 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10565 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq10565
    | (have j0 := eq10565 X0 X1 X2
       grind)
    | exact resolve eq10565 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10565
  have eq92808 : ∀ X0 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3017 X0 x
       have i₂ := eq316 X0 x X2
       grind)
    | exact superpose eq316 eq3017
    | (have j1 := eq316 X0 x X2
       grind)
    | exact resolve eq3017 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq3017
  have eq94650 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92808 (σ X0) X1
       have i₂ := eq688 X0
       grind)
    | exact superpose eq688 eq92808
    | (have j0 := eq92808 (σ X0) X1
       grind)
    | exact resolve eq92808 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92808
  have eq95101 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94650 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq94650
    | (have j0 := eq94650 X0 X1
       grind)
    | exact resolve eq94650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94650
  have eq95185 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95101 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq95101
    | (have j0 := eq95101 X0 X1
       grind)
    | exact resolve eq95101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95101
  have eq164745 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq10594 X0 y x
       grind)
    | exact superpose eq10594 eq14
    | (have j1 := eq10594 X0 y x
       grind)
    | exact resolve eq14 eq10594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10594
  have eq164749 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq164745 X0
       have j1 := eq6050 X0 y X0
       grind)
    | (have r₁ := eq164745 X0
       have r₂ := eq6050 x y x
       grind)
    | exact resolve eq164745 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050 eq164745
  have eq165029 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (k X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6279 X1 X2 X0
       have i₂ := eq164749 X0
       grind)
    | exact superpose eq164749 eq6279
    | exact resolve eq6279 eq164749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279
  have eq165175 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq688 X0
       have i₂ := eq164749 (σ X0)
       grind)
    | exact superpose eq164749 eq688
    | exact resolve eq688 eq164749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq165193 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (σ (k (τ X0) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 X0 X1 X2
       have i₂ := eq164749 (τ X0)
       grind)
    | exact superpose eq164749 eq471
    | exact resolve eq471 eq164749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq165221 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1409 X0 y
       have i₂ := eq164749 X0
       grind)
    | exact superpose eq164749 eq1409
    | (have j0 := eq1409 X0 y
       grind)
    | exact resolve eq1409 eq164749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq164749
  have eq165237 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X1) X2))) = (k X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165193 X0 X1 X2
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq165193
    | exact resolve eq165193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq165193
  have eq165289 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq165237 X0 x x
       have i₂ := eq165029 X0 x x
       grind)
    | exact superpose eq165029 eq165237
    | exact resolve eq165237 eq165029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165029 eq165237
  have eq165648 : ∀ X0 : G, (k X0 y) = (M.op X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq95185 y X0
       have i₂ := eq165289 X0
       grind)
    | exact superpose eq165289 eq95185
    | (have j0 := eq95185 y x
       grind)
    | exact resolve eq95185 eq165289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95185 eq165289
  have eq225742 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq165648 (σ x)
       grind)
    | exact superpose eq165648 eq14
    | exact resolve eq14 eq165648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165648
  have eq225812 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq225742
       have i₂ := eq165175 x
       grind)
    | exact superpose eq165175 eq225742
    | exact resolve eq225742 eq165175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165175 eq225742
  have eq225889 : y = (M.op y y) := by
    first
    | (have r₁ := eq225812
       have r₂ := eq165221 x
       grind)
    | exact resolve eq225812 eq165221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165221 eq225812
  have eq225948 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq225889
       grind)
    | exact superpose eq225889 eq21
    | exact resolve eq21 eq225889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq226066 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1538 y X0
       have i₂ := eq225889
       grind)
    | exact superpose eq225889 eq1538
    | exact resolve eq1538 eq225889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq226376 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq226066 X0
       have i₂ := eq225889
       grind)
    | exact superpose eq225889 eq226066
    | exact resolve eq226066 eq225889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226066
  have eq226482 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq225948 X0
       have i₂ := eq225889
       grind)
    | exact superpose eq225889 eq225948
    | exact resolve eq225948 eq225889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225889 eq225948
  have eq229143 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq226376 (σ x)
       grind)
    | exact superpose eq226376 eq14
    | exact resolve eq14 eq226376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226376
  have eq229341 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq229143
       have i₂ := eq226482 x
       grind)
    | exact superpose eq226482 eq229143
    | exact resolve eq229143 eq226482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226482 eq229143
  have eq229342 : False := by grind
  exact eq229342

/-- `Equation1264`: `x = x ◇ (((y ◇ z) ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1264 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1264 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1264.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq23 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq249 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq24
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq24 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq581 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq1583 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq250
    | (have j0 := eq250 (M.op X0 X0)
       grind)
    | exact resolve eq250 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1598 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq250
    | (have j0 := eq250 (τ X0)
       grind)
    | exact resolve eq250 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq250
  have eq1611 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1598 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1598
    | (have j0 := eq1598 X0
       grind)
    | exact resolve eq1598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1626 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1617
    | (have j0 := eq1617 X0
       grind)
    | exact resolve eq1617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1815 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1611 X0
       grind)
    | exact superpose eq1611 eq24
    | exact resolve eq24 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1910 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1815 X0 X1
       have i₂ := eq632 X2 X0
       grind)
    | exact superpose eq632 eq1815
    | (have j1 := eq632 X2 X0
       grind)
    | exact resolve eq1815 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq1815
  have eq2053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq249 y X0 x
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 y X0 x
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq2083 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2053 X0
       have j1 := eq1910 y X0 x
       grind)
    | (have r₁ := eq2053 X0
       have r₂ := eq1910 y x x
       grind)
    | exact resolve eq2053 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910 eq2053
  have eq2098 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq129 (σ y) x
       have i₂ := eq2083 (σ y)
       grind)
    | exact superpose eq2083 eq129
    | exact resolve eq129 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq2122 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2083 (σ x)
       grind)
    | exact superpose eq2083 eq14
    | exact resolve eq14 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2144 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2098 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2098
    | exact resolve eq2098 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2271 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1626 y
       have i₂ := eq2144 y
       grind)
    | exact superpose eq2144 eq1626
    | (have j0 := eq1626 y
       grind)
    | (have r₁ := eq1626 y
       have r₂ := eq2144 y
       grind)
    | exact resolve eq1626 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq2144
  have eq2287 : y = (M.op y y) := by grind
  clear eq2271
  have eq2397 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq24
    | exact resolve eq24 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2287
  have eq2913 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2122
       have i₂ := eq2397 x
       grind)
    | exact superpose eq2397 eq2122
    | exact resolve eq2122 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122 eq2397
  have eq2914 : False := by grind
  exact eq2914

/-- `Equation1267`: `x = x ◇ (((y ◇ z) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1267 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1267 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1267.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op (M.op X1 X2) X2) X1)
       have i₂ := eq8 (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq22 X0 x x X3
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq56 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (σ X1)
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq249 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq46 X2 X0
       grind)
    | exact superpose eq46 eq24
    | (have j1 := eq46 X2 X0
       grind)
    | exact resolve eq24 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq581 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq1583 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq250
    | (have j0 := eq250 (M.op X0 X0)
       grind)
    | exact resolve eq250 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1598 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq250 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq250
    | (have j0 := eq250 (τ X0)
       grind)
    | exact resolve eq250 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq250
  have eq1611 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1598 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1598
    | (have j0 := eq1598 X0
       grind)
    | exact resolve eq1598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1626 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1617 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1617
    | (have j0 := eq1617 X0
       grind)
    | exact resolve eq1617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1815 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1611 X0
       grind)
    | exact superpose eq1611 eq24
    | exact resolve eq24 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1910 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1815 X0 X1
       have i₂ := eq632 X2 X0
       grind)
    | exact superpose eq632 eq1815
    | (have j1 := eq632 X2 X0
       grind)
    | exact resolve eq1815 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq1815
  have eq2053 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq249 y X0 x
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 y X0 x
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq2083 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2053 X0
       have j1 := eq1910 y X0 x
       grind)
    | (have r₁ := eq2053 X0
       have r₂ := eq1910 y x x
       grind)
    | exact resolve eq2053 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910 eq2053
  have eq2098 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq129 (σ y) x
       have i₂ := eq2083 (σ y)
       grind)
    | exact superpose eq2083 eq129
    | exact resolve eq129 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq2122 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2083 (σ x)
       grind)
    | exact superpose eq2083 eq14
    | exact resolve eq14 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2144 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2098 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2098
    | exact resolve eq2098 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2271 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1626 y
       have i₂ := eq2144 y
       grind)
    | exact superpose eq2144 eq1626
    | (have j0 := eq1626 y
       grind)
    | (have r₁ := eq1626 y
       have r₂ := eq2144 y
       grind)
    | exact resolve eq1626 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq2144
  have eq2287 : y = (M.op y y) := by grind
  clear eq2271
  have eq2397 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq2287
       grind)
    | exact superpose eq2287 eq24
    | exact resolve eq24 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2287
  have eq2913 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2122
       have i₂ := eq2397 x
       grind)
    | exact superpose eq2397 eq2122
    | exact resolve eq2122 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122 eq2397
  have eq2914 : False := by grind
  exact eq2914
