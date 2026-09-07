import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4386 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4386 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq72 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (M.op X1 X1)
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq79
    | (have j0 := eq79 X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq79 (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0))
       have r₂ := eq8 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq79 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq26 X1 X1 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 (k X1 X1) X1
       have j1 := eq26 X2 X1 X2
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X2) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq26 X1 X1 X0
       grind)
    | exact superpose eq26 eq8
    | (have j1 := eq26 (M.op (M.op X0 X1) X0) X1 X2
       grind)
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq301 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq9
    | (have j1 := eq29 X1 X0
       grind)
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq72
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq72 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq338
    | (have j0 := eq338 X0 X1
       grind)
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq1130 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1130
    | (have j0 := eq1130 X0 X1
       grind)
    | exact resolve eq1130 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq2342 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq73 X0 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2834 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq328
    | (have j0 := eq328 X1 X0
       have j1 := eq29 X0 X1
       grind)
    | exact resolve eq328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq328
  have eq2885 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2834 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2834
    | (have j0 := eq2834 X0 X1
       grind)
    | exact resolve eq2834 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq7202 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X0
       have i₂ := eq186 X1 X0 X0
       grind)
    | exact superpose eq186 eq137
    | (have j0 := eq137 X0 X0
       have j1 := eq186 X0 X0 x
       grind)
    | exact resolve eq137 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq7296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq10201 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq355 x y
       grind)
    | exact superpose eq355 eq14
    | (have j1 := eq355 x y
       grind)
    | exact resolve eq14 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10300 : y = (k x y) := by
    first
    | (have j1 := eq1480 x y
       grind)
    | (have r₁ := eq10201
       have r₂ := eq1480 x y
       grind)
    | exact resolve eq10201 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq11014 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1228 x y
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq1228
    | (have j0 := eq1228 x y
       grind)
    | exact resolve eq1228 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq185 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq12105 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq13543 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq13741 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq186 X2 X0 x
       have i₂ := eq12105 X0 x
       grind)
    | exact superpose eq12105 eq186
    | (have j0 := eq186 X0 X0 X2
       have j1 := eq12105 X0 x
       grind)
    | exact resolve eq186 eq12105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq13862 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq13741 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13741
  have eq72612 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq151 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq151
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq12 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact resolve eq151 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq131859 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2885 x y
       grind)
    | exact superpose eq2885 eq14
    | (have j1 := eq2885 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2885 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2885 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885
  have eq131872 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq131859
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq131859
    | exact resolve eq131859 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131859
  have eq132684 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq131872
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq131872
    | (have r₁ := eq131872
       have r₂ := eq11014
       grind)
    | exact resolve eq131872 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131872
  have eq132685 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq132684
  have eq132818 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq132685
       grind)
    | exact superpose eq132685 eq9
    | exact resolve eq9 eq132685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132685
  have eq132833 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq132818
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq132818
    | exact resolve eq132818 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132818
  have eq133062 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq132833
       grind)
    | exact superpose eq132833 eq27
    | exact resolve eq27 eq132833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq132833
  have eq133092 : x = (M.op y y) ∨ x = y := by grind
  clear eq133062
  have eq133343 : x = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq7296 y y
       have i₂ := eq133092
       grind)
    | exact superpose eq133092 eq7296
    | exact resolve eq7296 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq133350 : y = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq13862 y y
       have i₂ := eq133092
       grind)
    | exact superpose eq133092 eq13862
    | exact resolve eq13862 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13862
  have eq138608 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13543 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13543
    | exact resolve eq13543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq138616 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138608 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq138608
    | (have j0 := eq138608 X0 X1
       grind)
    | exact resolve eq138608 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138608
  have eq138617 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138616 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138616
    | (have j0 := eq138616 X0 X1
       grind)
    | exact resolve eq138616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138616
  have eq138618 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op (M.op X1 X0) X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138617 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq138617
    | (have j0 := eq138617 X0 X1
       grind)
    | exact resolve eq138617 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq138617
  have eq138619 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138618 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138618
    | (have j0 := eq138618 X0 X1
       grind)
    | exact resolve eq138618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138618
  have eq139362 : x = y ∨ x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq133343
       have i₂ := eq133350
       grind)
    | exact superpose eq133350 eq133343
    | exact resolve eq133343 eq133350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133343 eq133350
  have eq139381 : x = (k y y) ∨ x = y := by grind
  clear eq139362
  have eq141046 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2342 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq141047 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq141046 X0 X1
       have j1 := eq301 X1 X0
       grind)
    | (have r₁ := eq141046 (k X1 X1) X0
       have r₂ := eq301 X0 X1
       grind)
    | (have r₁ := eq141046 X0 (σ (k X1 X1))
       have r₂ := eq301 (σ X0) X1
       grind)
    | (have r₁ := eq141046 X1 X0
       have r₂ := eq301 X0 X1
       grind)
    | exact resolve eq141046 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq141046
  have eq141205 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq141047 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq141047 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq141047 eq16
    | (have j1 := eq141047 (τ X1) X0
       grind)
    | exact resolve eq16 eq141047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141206 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq141047 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq141047 X0 (σ X0)
       grind)
    | exact superpose eq141047 eq9
    | (have j1 := eq141047 X1 X0
       grind)
    | exact resolve eq9 eq141047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141047
  have eq141247 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq141205 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq141205
    | (have j0 := eq141205 X0 X1
       grind)
    | exact resolve eq141205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141205
  have eq141253 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq141247 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq141247
    | (have j0 := eq141247 X0 X1
       grind)
    | exact resolve eq141247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141247
  have eq142165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq141206 (σ X0) X1
       grind)
    | exact superpose eq141206 eq13
    | (have j1 := eq141206 (σ X0) X1
       grind)
    | exact resolve eq13 eq141206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141206
  have eq142181 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq142165 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq142165
    | (have j0 := eq142165 X0 X1
       grind)
    | exact resolve eq142165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142165
  have eq143323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq142181 x y
       grind)
    | exact superpose eq142181 eq14
    | (have j1 := eq142181 x y
       grind)
    | exact resolve eq14 eq142181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143366 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq143323
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq143323
    | exact resolve eq143323 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300 eq143323
  have eq143411 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq143366
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq143366
    | (have r₁ := eq143366
       have r₂ := eq11014
       grind)
    | exact resolve eq143366 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014 eq143366
  have eq143413 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq143411
  have eq143534 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq143413
       grind)
    | exact superpose eq143413 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq143413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143413
  have eq143572 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq143534
  have eq144216 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq143572
  have eq144239 : x = (M.op y y) := by
    first
    | (have r₁ := eq144216
       have r₂ := eq133092
       grind)
    | exact resolve eq144216 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133092 eq144216
  have eq144424 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq8
    | exact resolve eq8 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144434 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq61
    | exact resolve eq61 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq144595 : x ≠ y ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq72612 y y
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq72612
    | (have j0 := eq72612 y y
       grind)
    | exact resolve eq72612 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72612
  have eq144603 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq144595
       have r₂ := eq139381
       grind)
    | exact resolve eq144595 eq139381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144595
  have eq146413 : x ≠ y ∨ x = (k y y) := by grind
  clear eq144603
  have eq146445 : x = (k y y) := by
    first
    | (have r₁ := eq146413
       have r₂ := eq139381
       grind)
    | exact resolve eq146413 eq139381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139381 eq146413
  have eq146606 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq141253 X0 y
       have i₂ := eq146445
       grind)
    | exact superpose eq146445 eq141253
    | (have j0 := eq141253 X0 y
       grind)
    | exact resolve eq141253 eq146445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146800 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq146606 (τ X0)
       grind)
    | exact superpose eq146606 eq16
    | (have j1 := eq146606 (τ X0)
       grind)
    | exact resolve eq16 eq146606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq146606
  have eq171544 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq146800 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146800
    | exact resolve eq146800 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146800
  have eq171570 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq171544 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq171544
    | (have j0 := eq171544 X0
       grind)
    | exact resolve eq171544 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171544
  have eq191119 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq138619 X0 x
       have i₂ := eq12105 X0 x
       grind)
    | exact superpose eq12105 eq138619
    | (have j0 := eq138619 X0 x
       have j1 := eq12105 X0 x
       grind)
    | exact resolve eq138619 eq12105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12105 eq138619
  have eq191157 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq191119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191119
  have eq191175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq191157 X0
       have j1 := eq141253 X0 X0
       grind)
    | (have r₁ := eq191157 X0
       have r₂ := eq141253 X0 X0
       grind)
    | (have r₁ := eq191157 (k x x)
       have r₂ := eq141253 (k (k x x) (k x x)) x
       grind)
    | exact resolve eq191157 eq141253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141253 eq191157
  have eq191545 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq191175 (σ X0)
       grind)
    | exact superpose eq191175 eq13
    | exact resolve eq13 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191639 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq191545 X0
       have i₂ := eq191175 X0
       grind)
    | exact superpose eq191175 eq191545
    | exact resolve eq191545 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191545
  have eq192764 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq191639 X0
       grind)
    | exact superpose eq191639 eq8
    | exact resolve eq8 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192862 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0) (σ X0)
       have i₂ := eq191639 X0
       grind)
    | exact superpose eq191639 eq18
    | exact resolve eq18 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq197432 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq192764 y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq192764
    | exact resolve eq192764 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192764
  have eq198065 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ X0)) ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq197432 (σ X0)
       have i₂ := eq142181 X0 y
       grind)
    | exact superpose eq142181 eq197432
    | (have j1 := eq142181 X0 y
       grind)
    | exact resolve eq197432 eq142181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198610 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq198065 X0
       have i₂ := eq146445
       grind)
    | exact superpose eq146445 eq198065
    | (have j0 := eq198065 X0
       grind)
    | exact resolve eq198065 eq146445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146445 eq198065
  have eq199065 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq192862 y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq192862
    | exact resolve eq192862 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144239 eq192862
  have eq199960 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq197432 x
       have i₂ := eq199065 x
       grind)
    | exact superpose eq199065 eq197432
    | exact resolve eq197432 eq199065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197432 eq199065
  have eq200848 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq355 y x
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq355
    | (have j0 := eq355 y x
       grind)
    | exact resolve eq355 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq200859 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq142181 y x
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq142181
    | (have j0 := eq142181 y x
       grind)
    | exact resolve eq142181 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142181
  have eq200986 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq200859
       have i₂ := eq191175 x
       grind)
    | exact superpose eq191175 eq200859
    | exact resolve eq200859 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191175 eq200859
  have eq206825 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200848
       grind)
    | exact superpose eq200848 eq14
    | exact resolve eq14 eq200848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200848
  have eq206905 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq206825
       have i₂ := eq1480 y x
       grind)
    | exact superpose eq1480 eq206825
    | (have j1 := eq1480 y x
       grind)
    | exact resolve eq206825 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq206825
  have eq206910 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) := by grind
  clear eq206905
  have eq206915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq206910
       have i₂ := eq144424
       grind)
    | exact superpose eq144424 eq206910
    | exact resolve eq206910 eq144424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206910
  have eq206916 : x = (k y x) := by grind
  clear eq206915
  have eq206960 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1228 y x
       have i₂ := eq206916
       grind)
    | exact superpose eq206916 eq1228
    | (have j0 := eq1228 y x
       grind)
    | exact resolve eq1228 eq206916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq206994 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq206960
       have i₂ := eq144424
       grind)
    | exact superpose eq144424 eq206960
    | exact resolve eq206960 eq144424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144424 eq206960
  have eq212257 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200986
       grind)
    | exact superpose eq200986 eq14
    | exact resolve eq14 eq200986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200986
  have eq212298 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq212257
       have i₂ := eq206916
       grind)
    | exact superpose eq206916 eq212257
    | exact resolve eq212257 eq206916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206916 eq212257
  have eq212313 : y = (M.op x x) := by
    first
    | (have r₁ := eq212298
       have r₂ := eq206994
       grind)
    | exact resolve eq212298 eq206994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206994 eq212298
  have eq212346 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq19
    | exact resolve eq19 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212617 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq19
    | exact resolve eq19 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq218148 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq144434 X0
       have i₂ := eq212346 X0
       grind)
    | exact superpose eq212346 eq144434
    | exact resolve eq144434 eq212346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212346
  have eq242975 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq198610 X0
       have i₂ := eq171570 X0
       grind)
    | exact superpose eq171570 eq198610
    | (have j0 := eq198610 X0
       have j1 := eq171570 X0
       grind)
    | exact resolve eq198610 eq171570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171570 eq198610
  have eq243013 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq242975 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242975
  have eq243052 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq243013 X0
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq243013
    | (have j0 := eq243013 X0
       grind)
    | exact resolve eq243013 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199960 eq243013
  have eq253620 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq243052 (M.op x y)
       have i₂ := eq212617
       grind)
    | exact superpose eq212617 eq243052
    | (have j0 := eq243052 (M.op x y)
       grind)
    | exact resolve eq243052 eq212617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212617 eq243052
  have eq253672 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253620
       have i₂ := eq191639 (M.op x y)
       grind)
    | exact superpose eq191639 eq253620
    | exact resolve eq253620 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253620
  have eq253675 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253672
       have i₂ := eq144434 x
       grind)
    | exact superpose eq144434 eq253672
    | exact resolve eq253672 eq144434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144434 eq253672
  have eq253677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253675
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq253675
    | exact resolve eq253675 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253675
  have eq253679 : x = (M.op x y) := by
    first
    | (have r₁ := eq253677
       have r₂ := eq14
       grind)
    | exact resolve eq253677 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253677
  have eq253833 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq218148 x
       have i₂ := eq253679
       grind)
    | exact superpose eq253679 eq218148
    | exact resolve eq218148 eq253679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218148
  have eq254856 : y = (M.op x y) := by
    first
    | (have i₁ := eq253833
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq253833
    | exact resolve eq253833 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212313 eq253833
  have eq255289 : x = y := by
    first
    | (have i₁ := eq254856
       have i₂ := eq253679
       grind)
    | exact superpose eq253679 eq254856
    | exact resolve eq254856 eq253679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253679 eq254856
  have eq256650 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255289
       grind)
    | exact superpose eq255289 eq14
    | exact resolve eq14 eq255289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255289
  have eq257140 : False := by grind
  exact eq257140

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq101 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq26
    | (have j0 := eq26 X1 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq158 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq27 X1 X0 x
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq27 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X1 X0 x
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op X2 X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq27 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq27 eq13
    | (have j1 := eq27 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X0 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq800 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq932 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq1929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq294
       have i₂ := eq932 y x
       grind)
    | exact superpose eq932 eq294
    | (have j1 := eq932 y x
       grind)
    | (have r₁ := eq294
       have r₂ := eq932 y x
       grind)
    | exact resolve eq294 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq294
       have i₂ := eq876 y x
       grind)
    | exact superpose eq876 eq294
    | (have j1 := eq876 (σ y) (σ x)
       grind)
    | (have r₁ := eq294
       have r₂ := eq876 y x
       grind)
    | exact resolve eq294 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1931 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1930
  have eq1932 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1929
  have eq1943 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq90
    | exact resolve eq90 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1968 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1943
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1943
    | exact resolve eq1943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq2011 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq309 x x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq309
    | exact resolve eq309 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq2040 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2011
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2011
    | exact resolve eq2011 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2058 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq876 y x
       have i₂ := eq1968
       grind)
    | exact superpose eq1968 eq876
    | (have j0 := eq876 y x
       grind)
    | exact resolve eq876 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq1968
  have eq2059 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq2058
  have eq2646 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq90
    | exact resolve eq90 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2677 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2646
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2646
    | exact resolve eq2646 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2678 : y = (k x y) := by grind
  clear eq2677
  have eq2872 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq101 y x X0
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq101
    | (have j0 := eq101 y x X0
       grind)
    | exact resolve eq101 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq2678
  have eq2874 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq3227 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq2874 (τ X0)
       grind)
    | exact superpose eq2874 eq16
    | exact resolve eq16 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq2874
  have eq11467 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq187 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq11959 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2040
       grind)
    | exact superpose eq2040 eq9
    | exact resolve eq9 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq12015 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11959
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11959
    | exact resolve eq11959 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11959
  have eq12389 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq12015
       grind)
    | exact superpose eq12015 eq28
    | exact resolve eq28 eq12015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12015
  have eq12409 : y = (M.op x x) ∨ x = y := by grind
  clear eq12389
  have eq12673 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq8
    | exact resolve eq8 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13142 : (M.op x y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12673 x
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq12673
    | exact resolve eq12673 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12673
  have eq13241 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq13142
  have eq14849 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq311
  have eq30652 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3227 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3227
    | exact resolve eq3227 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq30768 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30652 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq30652
    | exact resolve eq30652 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30652
  have eq45650 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0
       have i₂ := eq72 (σ X0) X1
       grind)
    | exact superpose eq72 eq90
    | (have j1 := eq72 (σ X1) X0
       grind)
    | exact resolve eq90 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq90
  have eq45860 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq45650 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45650
    | (have j0 := eq45650 X0 X1
       grind)
    | exact resolve eq45650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45650
  have eq45983 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45860 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq45860
    | (have j0 := eq45860 X0 X1
       grind)
    | exact resolve eq45860 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45860
  have eq49747 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45983 x x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq45983
    | (have j0 := eq45983 x x
       grind)
    | exact resolve eq45983 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45983
  have eq49851 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49747
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq49747
    | exact resolve eq49747 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49747
  have eq57387 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq49851
  have eq57423 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq57387
       have r₂ := eq12409
       grind)
    | exact resolve eq57387 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57387
  have eq58863 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq331 x
       have i₂ := eq57423
       grind)
    | exact superpose eq57423 eq331
    | (have j0 := eq331 x
       grind)
    | exact resolve eq331 eq57423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq57423
  have eq58890 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq58863
  have eq64872 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq58890
       grind)
    | exact superpose eq58890 eq8
    | exact resolve eq8 eq58890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58890
  have eq124398 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64872 (σ x)
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq64872
    | exact resolve eq64872 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq64872
  have eq124521 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq124398
  have eq124563 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq124521
       grind)
    | exact superpose eq124521 eq14
    | exact resolve eq14 eq124521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124521
  have eq124588 : y = (M.op x x) := by
    first
    | (have r₁ := eq124563
       have r₂ := eq2059
       grind)
    | exact resolve eq124563 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq124563
  have eq124598 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq8
    | exact resolve eq8 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124601 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq18
    | exact resolve eq18 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq124958 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq124598 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq124598
    | exact resolve eq124598 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126286 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14849 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126287 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq126286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126286
  have eq126348 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq126287 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126287
    | exact resolve eq126287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126578 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq124598 (σ X0)
       have i₂ := eq126287 X0
       grind)
    | exact superpose eq126287 eq124598
    | exact resolve eq124598 eq126287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126579 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124601 (σ X0) X1
       have i₂ := eq126287 X0
       grind)
    | exact superpose eq126287 eq124601
    | exact resolve eq124601 eq126287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126753 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq126348 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq126348
    | exact resolve eq126348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126348
  have eq126811 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq126753 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126753
    | exact resolve eq126753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126753
  have eq128066 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126579 X0 X1
       have i₂ := eq126811 X0
       grind)
    | exact superpose eq126811 eq126579
    | exact resolve eq126579 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126579
  have eq130488 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq128066 x X0
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq128066
    | exact resolve eq128066 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130491 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq128066 x X0
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq128066
    | exact resolve eq128066 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12409 eq128066
  have eq131225 : (σ (k y y)) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq126287 y
       have i₂ := eq130488 (σ y)
       grind)
    | exact superpose eq130488 eq126287
    | exact resolve eq126287 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126287
  have eq131369 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 (σ y) X0
       have i₂ := eq130488 X0
       grind)
    | exact superpose eq130488 eq84
    | (have j0 := eq84 y X0
       grind)
    | exact resolve eq84 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq131580 : (M.op y (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq131225
       have i₂ := eq126811 y
       grind)
    | exact superpose eq126811 eq131225
    | exact resolve eq131225 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131225
  have eq137654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op y (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11467 X0 X1 x
       have i₂ := eq124601 x (σ X0)
       grind)
    | exact superpose eq124601 eq11467
    | (have j0 := eq11467 X0 X1 x
       grind)
    | exact resolve eq11467 eq124601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq124601
  have eq137776 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14849 y X0
       have i₂ := eq130491 (σ y)
       grind)
    | exact superpose eq130491 eq14849
    | (have j0 := eq14849 y X0
       grind)
    | exact resolve eq14849 eq130491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14849 eq130491
  have eq138041 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq137776 X0
       have j1 := eq137654 y X0
       grind)
    | (have r₁ := eq137776 x
       have r₂ := eq137654 y x
       grind)
    | exact resolve eq137776 eq137654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137654 eq137776
  have eq138138 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq138041 X0
       have i₂ := eq130488 (σ X0)
       grind)
    | exact superpose eq130488 eq138041
    | exact resolve eq138041 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130488 eq138041
  have eq139114 : ∀ X0 : G, (M.op y (M.op y y)) ≠ X0 ∨ (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq131369 X0
       have i₂ := eq158 y X0
       grind)
    | (have i₁ := eq131369 (M.op y y)
       have i₂ := eq158 y x
       grind)
    | exact superpose eq158 eq131369
    | (have j0 := eq131369 X0
       have j1 := eq158 y X0
       grind)
    | (have r₁ := eq131369 (M.op y y)
       have r₂ := eq158 y y
       grind)
    | (have r₁ := eq131369 (M.op y (M.op y y))
       have r₂ := eq158 y (M.op y (M.op y y))
       grind)
    | exact resolve eq131369 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq131369
  have eq139131 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq139114 X0
       have i₂ := eq124598 y
       grind)
    | exact superpose eq124598 eq139114
    | (have j0 := eq139114 X0
       grind)
    | (have r₁ := eq139114 (M.op y y)
       have r₂ := eq124598 y
       grind)
    | (have r₁ := eq139114 (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))
       have r₂ := eq124598 (M.op y y)
       grind)
    | exact resolve eq139114 eq124598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124598 eq139114
  have eq139135 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq139131 X0
       have j1 := eq12 y X0
       grind)
    | (have r₁ := eq139131 x
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq139131 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op y y)
       grind)
    | (have r₁ := eq139131 (k y y)
       have r₂ := eq12 y y
       grind)
    | exact resolve eq139131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139131
  have eq143468 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq126578 X0
       have i₂ := eq126811 X0
       grind)
    | exact superpose eq126811 eq126578
    | exact resolve eq126578 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126578 eq126811
  have eq145341 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq143468 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq143468
    | exact resolve eq143468 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143468
  have eq145709 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq145341
       grind)
    | exact superpose eq145341 eq14
    | exact resolve eq14 eq145341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145341
  have eq153384 : ∀ X0 : G, (k (σ y) X0) = (M.op y (σ (τ X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq138138 (τ X0)
       grind)
    | exact superpose eq138138 eq17
    | exact resolve eq17 eq138138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153392 : (M.op y (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30768 y
       have i₂ := eq138138 x
       grind)
    | exact superpose eq138138 eq30768
    | exact resolve eq30768 eq138138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30768
  have eq153421 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq153392
       have i₂ := eq124958
       grind)
    | exact superpose eq124958 eq153392
    | exact resolve eq153392 eq124958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153392
  have eq153429 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq153384 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153384
    | exact resolve eq153384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153384
  have eq153471 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq153421
       have r₂ := eq145709
       grind)
    | exact resolve eq153421 eq145709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153421
  have eq154437 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38 y X0
       have i₂ := eq153429 X0
       grind)
    | exact superpose eq153429 eq38
    | exact resolve eq38 eq153429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq153429
  have eq155518 : (τ (M.op x y)) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq154437 x
       have i₂ := eq13241
       grind)
    | exact superpose eq13241 eq154437
    | exact resolve eq154437 eq13241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13241 eq154437
  have eq155594 : (τ (M.op x y)) = (k y (τ x)) ∨ x = y := by grind
  clear eq155518
  have eq155917 : (τ y) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq155594
       have i₂ := eq153471
       grind)
    | exact superpose eq153471 eq155594
    | exact resolve eq155594 eq153471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153471 eq155594
  have eq155935 : (τ y) = (k y (τ x)) ∨ x = y := by grind
  clear eq155917
  have eq156104 : (σ (τ y)) = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq17 x y
       have i₂ := eq155935
       grind)
    | exact superpose eq155935 eq17
    | exact resolve eq17 eq155935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq155935
  have eq156159 : y = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq156104
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq156104
    | exact resolve eq156104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156104
  have eq172397 : x = y ∨ x = y ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq156159
       have i₂ := eq139135 x
       grind)
    | exact superpose eq139135 eq156159
    | (have j1 := eq139135 x
       grind)
    | exact resolve eq156159 eq139135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139135 eq156159
  have eq172433 : x = y ∨ (M.op y x) = (k y x) := by grind
  clear eq172397
  have eq172454 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq172433
       have i₂ := eq124958
       grind)
    | exact superpose eq124958 eq172433
    | exact resolve eq172433 eq124958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124958 eq172433
  have eq172504 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq138138 x
       have i₂ := eq172454
       grind)
    | exact superpose eq172454 eq138138
    | exact resolve eq138138 eq172454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138138 eq172454
  have eq172528 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = y := by grind
  clear eq172504
  have eq172532 : x = y := by
    first
    | (have r₁ := eq172528
       have r₂ := eq145709
       grind)
    | exact resolve eq172528 eq145709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172528
  have eq172628 : (σ (M.op x x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq131580
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq131580
    | exact resolve eq131580 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131580
  have eq172681 : (σ (M.op x x)) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq145709
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq145709
    | exact resolve eq145709 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145709
  have eq172708 : (σ y) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq172681
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq172681
    | exact resolve eq172681 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172681
  have eq172734 : (σ y) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq172628
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq172628
    | exact resolve eq172628 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124588 eq172628
  have eq172777 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq172708
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq172708
    | exact resolve eq172708 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172708
  have eq172795 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq172734
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq172734
    | exact resolve eq172734 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172532 eq172734
  have eq172818 : False := by grind
  exact eq172818

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq133 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq148 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133
    | exact resolve eq133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq281 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq148 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq148
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq347 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq338
    | (have j0 := eq338 X0
       grind)
    | exact resolve eq338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq953 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2014 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq79 X0 X1
       grind)
    | exact resolve eq31 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2018 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq8
    | (have j1 := eq79 X0 X0
       grind)
    | exact resolve eq8 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2020 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1107 y x
       grind)
    | exact superpose eq1107 eq333
    | (have j1 := eq1107 y x
       grind)
    | (have r₁ := eq333
       have r₂ := eq1107 y x
       grind)
    | exact resolve eq333 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq2283 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1042 y x
       grind)
    | exact superpose eq1042 eq333
    | (have j1 := eq1042 (σ y) (σ x)
       grind)
    | (have r₁ := eq333
       have r₂ := eq1042 y x
       grind)
    | exact resolve eq333 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq2284 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2283
  have eq2285 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2282
  have eq2295 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq148
    | exact resolve eq148 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2317 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85 (σ x) (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq85
    | (have j0 := eq85 (σ x) (σ x)
       grind)
    | exact resolve eq85 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2319 : (σ x) = (σ (k x x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2317
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq2317
    | exact resolve eq2317 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2322 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2295
    | exact resolve eq2295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2407 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1042 y x
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq1042
    | (have j0 := eq1042 y x
       grind)
    | exact resolve eq1042 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq2322
  have eq2408 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2407
  have eq3261 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2285
       grind)
    | exact superpose eq2285 eq148
    | exact resolve eq148 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq2285
  have eq3296 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3261
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3261
    | exact resolve eq3261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3297 : x = (k x y) := by grind
  clear eq3296
  have eq4199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq4274 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4199 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq4199
    | (have j0 := eq4199 X0 X1
       grind)
    | exact resolve eq4199 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq12744 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq281 (σ X1) X0
       grind)
    | exact superpose eq281 eq23
    | (have j1 := eq281 (σ X1) X0
       grind)
    | exact resolve eq23 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq12774 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12744 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12744
    | (have j0 := eq12744 X0 X1
       grind)
    | exact resolve eq12744 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12813 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12774 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq12774
    | (have j0 := eq12774 X0 X1
       grind)
    | exact resolve eq12774 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774
  have eq33983 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12813 x x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq12813
    | (have j0 := eq12813 x x
       grind)
    | exact resolve eq12813 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12813
  have eq34072 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33983
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33983
    | exact resolve eq33983 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33983
  have eq42409 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4274 x x
       have i₂ := eq34072
       grind)
    | exact superpose eq34072 eq4274
    | exact resolve eq4274 eq34072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274 eq34072
  have eq42413 : x = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq42409
  have eq53884 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq379 x
       have i₂ := eq42413
       grind)
    | exact superpose eq42413 eq379
    | (have j0 := eq379 x
       grind)
    | exact resolve eq379 eq42413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq42413
  have eq53921 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq53884
       have r₂ := eq2319
       grind)
    | exact resolve eq53884 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq53884
  have eq53925 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq370 x
       grind)
    | (have r₁ := eq53921
       have r₂ := eq370 x
       grind)
    | exact resolve eq53921 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53921
  have eq55078 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq2284
    | exact resolve eq2284 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55098 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq8
    | exact resolve eq8 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53925
  have eq55174 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq55078
  have eq56135 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq8
    | exact resolve eq8 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59605 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56135 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq56135
    | exact resolve eq56135 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56135
  have eq59670 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq59605
  have eq65106 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55098 (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq55098
    | exact resolve eq55098 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq55098
  have eq65218 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq65106
  have eq65255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65218
       grind)
    | exact superpose eq65218 eq14
    | exact resolve eq14 eq65218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65218
  have eq65315 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65255
       have i₂ := eq2408
       grind)
    | exact superpose eq2408 eq65255
    | exact resolve eq65255 eq2408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408 eq65255
  have eq65317 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq65315
  have eq65319 : y = (M.op x x) := by
    first
    | (have r₁ := eq65317
       have r₂ := eq55174
       grind)
    | exact resolve eq65317 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55174 eq65317
  have eq65358 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq8
    | exact resolve eq8 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65361 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq18
    | exact resolve eq18 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq65375 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 x X0
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq68
    | exact resolve eq68 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71262 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq65375 y
       have i₂ := eq65358 y
       grind)
    | exact superpose eq65358 eq65375
    | exact resolve eq65375 eq65358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65358 eq65375
  have eq71319 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq370 (M.op y y)
       have i₂ := eq71262
       grind)
    | exact superpose eq71262 eq370
    | (have j0 := eq370 (M.op y y)
       grind)
    | exact resolve eq370 eq71262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71349 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
  clear eq71319
  have eq75336 : ∀ X0 : G, (τ (σ (M.op y y))) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq347 (M.op y y) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq347
    | (have j0 := eq347 (M.op y y) X0
       grind)
    | exact resolve eq347 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq75474 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq65361 (σ (M.op y y)) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq65361
    | exact resolve eq65361 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75611 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75336 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq75336
    | (have j0 := eq75336 X0
       grind)
    | exact resolve eq75336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75336
  have eq75673 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq75611 X0
       have i₂ := eq75474 (σ X0)
       grind)
    | exact superpose eq75474 eq75611
    | (have j0 := eq75611 X0
       grind)
    | exact resolve eq75611 eq75474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75474 eq75611
  have eq78200 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq78201 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq78200 X0 X1
       have j1 := eq318 X1 X0
       grind)
    | (have r₁ := eq78200 (k X1 X1) X0
       have r₂ := eq318 X0 X1
       grind)
    | (have r₁ := eq78200 X0 (σ (k X1 X1))
       have r₂ := eq318 (σ X0) X1
       grind)
    | (have r₁ := eq78200 X1 X0
       have r₂ := eq318 X0 X1
       grind)
    | exact resolve eq78200 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq78200
  have eq78248 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq78201 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq78201 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq78201 eq16
    | (have j1 := eq78201 (τ X1) X0
       grind)
    | exact resolve eq16 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq78249 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq78201 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq78201 X0 (σ X0)
       grind)
    | exact superpose eq78201 eq9
    | (have j1 := eq78201 X1 X0
       grind)
    | exact resolve eq9 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78201
  have eq78268 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78248 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq78248
    | (have j0 := eq78248 X0 X1
       grind)
    | exact resolve eq78248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78248
  have eq78277 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78268 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78268
    | (have j0 := eq78268 X0 X1
       grind)
    | exact resolve eq78268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78268
  have eq78432 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq78277 (τ X1) X0
       grind)
    | exact superpose eq78277 eq17
    | (have j1 := eq78277 (τ X1) X0
       grind)
    | exact resolve eq17 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq78472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2014
       have i₂ := eq78277 y x
       grind)
    | exact superpose eq78277 eq2014
    | (have j1 := eq78277 y x
       grind)
    | exact resolve eq2014 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014 eq78277
  have eq78599 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq78472
  have eq80736 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq13
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq13 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80740 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq23
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq23 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq78249
  have eq80742 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80740 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80740
    | (have j0 := eq80740 X0 X1
       grind)
    | exact resolve eq80740 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80740
  have eq80744 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80736 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80736
    | (have j0 := eq80736 X0 X1
       grind)
    | exact resolve eq80736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80736
  have eq80773 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80742 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80742
    | (have j0 := eq80742 X0 X1
       grind)
    | exact resolve eq80742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80742
  have eq81732 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq80744 x y
       grind)
    | exact superpose eq80744 eq14
    | (have j1 := eq80744 x y
       grind)
    | exact resolve eq14 eq80744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80744
  have eq81816 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq81732
       have i₂ := eq3297
       grind)
    | exact superpose eq3297 eq81732
    | exact resolve eq81732 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq81732
  have eq81838 : y = (k x x) := by
    first
    | (have r₁ := eq81816
       have r₂ := eq78599
       grind)
    | exact resolve eq81816 eq78599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78599 eq81816
  have eq81911 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq370 x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq370
    | (have j0 := eq370 x
       grind)
    | exact resolve eq370 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq81925 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2018 x x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq2018
    | exact resolve eq2018 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq82005 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81925 x
       have i₂ := eq65361 x (σ x)
       grind)
    | exact superpose eq65361 eq81925
    | exact resolve eq81925 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81925
  have eq88307 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82005
       grind)
    | exact superpose eq82005 eq14
    | exact resolve eq14 eq82005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82005
  have eq108866 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78432 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78432
    | exact resolve eq78432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78432
  have eq108935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108866 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq108866
    | (have j0 := eq108866 X0 X1
       grind)
    | exact resolve eq108866 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108866
  have eq109103 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (σ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq71262
       have i₂ := eq108935 X0 (M.op y y)
       grind)
    | (have i₁ := eq71262
       have i₂ := eq108935 (k (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq108935 eq71262
    | (have j1 := eq108935 X0 (M.op y y)
       grind)
    | exact resolve eq71262 eq108935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71262 eq108935
  have eq109117 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109103 X0
       have i₂ := eq65361 y X0
       grind)
    | exact superpose eq65361 eq109103
    | (have j0 := eq109103 X0
       grind)
    | exact resolve eq109103 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65361 eq109103
  have eq118141 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109117 X0
       have i₂ := eq75673 X0
       grind)
    | exact superpose eq75673 eq109117
    | (have j0 := eq109117 X0
       have j1 := eq75673 X0
       grind)
    | exact resolve eq109117 eq75673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75673 eq109117
  have eq118152 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq118141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118141
  have eq118182 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118152 x
       have i₂ := eq59670
       grind)
    | exact superpose eq59670 eq118152
    | (have j0 := eq118152 x
       grind)
    | exact resolve eq118152 eq59670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59670 eq118152
  have eq118256 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq118182
       have r₂ := eq88307
       grind)
    | exact resolve eq118182 eq88307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88307 eq118182
  have eq118283 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71349
       have i₂ := eq118256
       grind)
    | exact superpose eq118256 eq71349
    | exact resolve eq71349 eq118256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71349 eq118256
  have eq118554 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq118283
       have r₂ := eq81911
       grind)
    | exact resolve eq118283 eq81911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81911 eq118283
  have eq118709 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq2015 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq2015
    | (have j0 := eq2015 x x
       grind)
    | exact resolve eq2015 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq118716 : (k x x) = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq80773 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq80773
    | (have j0 := eq80773 x (τ (σ x))
       grind)
    | exact resolve eq80773 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80773
  have eq119003 : (σ x) = (σ (k x x)) := by grind
  clear eq118709
  have eq119219 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq118716
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq118716
    | exact resolve eq118716 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118716
  have eq119220 : x = (k x x) := by grind
  clear eq119219
  have eq119228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq119003
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq119003
    | exact resolve eq119003 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119003
  have eq119533 : x = y := by
    first
    | (have i₁ := eq81838
       have i₂ := eq119220
       grind)
    | exact superpose eq119220 eq81838
    | exact resolve eq81838 eq119220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81838 eq119220
  have eq119796 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119533
       grind)
    | exact superpose eq119533 eq14
    | exact resolve eq14 eq119533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119533
  have eq120107 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119796
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq119796
    | exact resolve eq119796 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65319 eq119796
  have eq120166 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq120107
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq120107
    | exact resolve eq120107 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118554 eq120107
  have eq120190 : False := by grind
  exact eq120190

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (M.op X1 X1)
       have i₂ := eq18 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X1 X1)
       have i₂ := eq18 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq22
  have eq80 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq92 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (k X0 (τ X1)) X2
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq38
    | exact resolve eq38 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq130 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq41 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq41
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (M.op X2 X2) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq26 (τ X0) X1 X2
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 (τ X0) X1 X2
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq221 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X1 ∨ (k (M.op X2 X2) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 (M.op X2 X2) X1
       have i₂ := eq18 X2 X1 X0
       grind)
    | (have i₁ := eq87 (M.op X2 X2) X1
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq87
    | (have j0 := eq87 (M.op X0 X0) X1
       grind)
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | (have i₁ := eq80 X0
       have i₂ := eq12 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq12 eq80
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X0
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq9
    | (have j1 := eq29 X1 X0
       grind)
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq80
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq80 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq370 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq374 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq357
    | (have j0 := eq357 X0 X1
       grind)
    | exact resolve eq357 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq805 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X3)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq52 X1 X2 X0 (M.op (M.op X1 X1) (M.op X2 X2))
       grind)
    | (have i₁ := eq8 X0 (M.op X2 X2)
       have i₂ := eq52 X0 X1 X2 (M.op X2 X2)
       grind)
    | exact superpose eq52 eq8
    | exact resolve eq8 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq952 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq370 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq370
    | (have j0 := eq370 (τ X0)
       grind)
    | exact resolve eq370 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq952 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq952
    | (have j0 := eq952 X0
       grind)
    | exact resolve eq952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq957 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq954 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq954
    | (have j0 := eq954 X0
       grind)
    | exact resolve eq954 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq969 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq957 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq957
    | (have j0 := eq957 (τ X0)
       grind)
    | exact resolve eq957 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq991 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq10
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1083 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq991
    | (have j0 := eq991 X0 X1
       grind)
    | exact resolve eq991 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq1183 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1
       have i₂ := eq1083 X0 (τ X1)
       grind)
    | (have i₁ := eq41 X0
       have i₂ := eq1083 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq1083 eq41
    | (have j1 := eq1083 X0 (τ X1)
       grind)
    | exact resolve eq41 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1183 X0 X1
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq1183
    | (have j0 := eq1183 X0 X1
       grind)
    | exact resolve eq1183 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq2084 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq8
    | (have j1 := eq81 X0 X0
       grind)
    | exact resolve eq8 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2085 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq81 X0 X0
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2573 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq347
    | exact resolve eq347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq2614 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2573 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2573
    | (have j0 := eq2573 X0 X1
       grind)
    | exact resolve eq2573 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq3425 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq130 X1 (σ X0)
       grind)
    | exact superpose eq130 eq13
    | (have j1 := eq130 X1 (σ X0)
       grind)
    | exact resolve eq13 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq3472 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3425 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3425
    | (have j0 := eq3425 X0 X1
       grind)
    | exact resolve eq3425 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq3693 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq3472 X0 (τ X1)
       grind)
    | exact superpose eq3472 eq16
    | (have j1 := eq3472 X0 (τ X1)
       grind)
    | exact resolve eq16 eq3472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq6312 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq957 (τ X0)
       have i₂ := eq282 X0 (τ X0)
       grind)
    | exact superpose eq282 eq957
    | (have j0 := eq957 (τ X0)
       have j1 := eq282 X0 (τ X0)
       grind)
    | (have r₁ := eq957 (τ X0)
       have r₂ := eq282 X0 (τ X0)
       grind)
    | exact resolve eq957 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq957
  have eq6343 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq6312 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6312
  have eq6358 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6343 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6343
    | (have j0 := eq6343 X0
       grind)
    | exact resolve eq6343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6988 : ∀ X0 X1 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op X1 X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0
       have i₂ := eq211 X0 (τ X0) X1
       grind)
    | exact superpose eq211 eq41
    | (have j1 := eq211 X0 (τ X0) X1
       grind)
    | exact resolve eq41 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq7275 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op X1 X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6988 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6988
    | (have j0 := eq6988 X0 X1
       grind)
    | exact resolve eq6988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq7375 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq374 x y
       grind)
    | exact superpose eq374 eq14
    | (have j1 := eq374 x y
       grind)
    | exact resolve eq14 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7446 : y = (k x y) := by
    first
    | (have j1 := eq1148 x y
       grind)
    | (have r₁ := eq7375
       have r₂ := eq1148 x y
       grind)
    | exact resolve eq7375 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq7375
  have eq7529 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq336 (τ X0) X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq336
    | (have j0 := eq336 (τ X0) X1
       grind)
    | exact resolve eq336 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq7606 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7529 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7529
    | (have j0 := eq7529 X0 X1
       grind)
    | exact resolve eq7529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq7612 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7606 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7606
    | (have j0 := eq7606 X0 X1
       grind)
    | exact resolve eq7606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq7624 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1083 x y
       have i₂ := eq7446
       grind)
    | exact superpose eq7446 eq1083
    | (have j0 := eq1083 x y
       grind)
    | exact resolve eq1083 eq7446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30265 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq1055 (τ X0) X0
       grind)
    | exact superpose eq1055 eq41
    | (have j1 := eq1055 (τ X0) X0
       grind)
    | exact resolve eq41 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1055
  have eq30371 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30265 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30265
    | (have j0 := eq30265 X0
       grind)
    | exact resolve eq30265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30265
  have eq49827 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1188 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1188
    | (have j0 := eq1188 X1 (σ X0)
       grind)
    | exact resolve eq1188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq50127 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49827 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq49827
    | (have j0 := eq49827 X0 X1
       grind)
    | exact resolve eq49827 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49827
  have eq50148 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50127 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq50127
    | (have j0 := eq50127 X0 X1
       grind)
    | exact resolve eq50127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50127
  have eq69555 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq370 (τ X0)
       have i₂ := eq3693 (τ X0) X0
       grind)
    | exact superpose eq3693 eq370
    | (have j0 := eq370 (τ X0)
       have j1 := eq3693 (τ X0) X0
       grind)
    | exact resolve eq370 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq69627 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq69555 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69555
    | (have j0 := eq69555 X0
       grind)
    | exact resolve eq69555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69555
  have eq69658 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq69627 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69627
    | (have j0 := eq69627 X0
       grind)
    | exact resolve eq69627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69627
  have eq69675 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq69658 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69658
    | (have j0 := eq69658 X0
       grind)
    | exact resolve eq69658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69658
  have eq69688 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq69675 X0
       have j1 := eq87 X0 X0
       grind)
    | (have r₁ := eq69675 x
       have r₂ := eq87 x x
       grind)
    | exact resolve eq69675 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69675
  have eq80362 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq50148 X0 X0
       grind)
    | exact superpose eq50148 eq370
    | (have j0 := eq370 X0
       have j1 := eq50148 X0 X0
       grind)
    | (have r₁ := eq370 x
       have r₂ := eq50148 x x
       grind)
    | exact resolve eq370 eq50148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80528 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq50148 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50148
  have eq80556 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80362 X0
       have j1 := eq370 X0
       grind)
    | (have r₁ := eq80362 X0
       have r₂ := eq370 X0
       grind)
    | exact resolve eq80362 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq80362
  have eq90159 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2084 (τ X0) X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq2084
    | exact resolve eq2084 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2084
  have eq90502 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90159 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90159
    | (have j0 := eq90159 X0 X1
       grind)
    | exact resolve eq90159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90159
  have eq90514 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (k X0 X0) X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90502 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90502
    | (have j0 := eq90502 X0 X1
       grind)
    | exact resolve eq90502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90502
  have eq103945 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (τ X1))) = X1 ∨ (k (k X1 X1) X1) = X1 ∨ (k (k X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30371 X1
       have i₂ := eq7275 X1 X0
       grind)
    | exact superpose eq7275 eq30371
    | (have j0 := eq30371 X1
       have j1 := eq7275 X1 X1
       grind)
    | exact resolve eq30371 eq7275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275 eq30371
  have eq104297 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (τ X1))) = X1 ∨ (k (k X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103945
  have eq107572 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k X0 (τ (σ X0))) (τ (σ X0))) ∨ (σ X0) = (σ (M.op (M.op X1 X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (σ X0) (σ X0)
       have i₂ := eq104297 X1 (σ X0)
       grind)
    | exact superpose eq104297 eq92
    | (have j1 := eq104297 X1 (σ X0)
       grind)
    | exact resolve eq92 eq104297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq104297
  have eq107682 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (σ (M.op (M.op X1 X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq107572 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107572
    | (have j0 := eq107572 X0 X1
       grind)
    | exact resolve eq107572 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107572
  have eq107737 : ∀ X0 X1 : G, (σ X0) = (σ (M.op (M.op X1 X1) X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107682 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107682
    | (have j0 := eq107682 X0 X1
       grind)
    | exact resolve eq107682 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107682
  have eq119588 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107737 X0 (M.op (M.op x x) (M.op x x))
       have i₂ := eq805 (M.op x x) x x X0
       grind)
    | exact superpose eq805 eq107737
    | (have j0 := eq107737 X0 x
       grind)
    | exact resolve eq107737 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq107737
  have eq126216 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2085 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq126217 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq126216 X0 X1
       have j1 := eq319 X1 X0
       grind)
    | (have r₁ := eq126216 (k X1 X1) X0
       have r₂ := eq319 X0 X1
       grind)
    | (have r₁ := eq126216 X0 (σ (k X1 X1))
       have r₂ := eq319 (σ X0) X1
       grind)
    | (have r₁ := eq126216 X1 X0
       have r₂ := eq319 X0 X1
       grind)
    | exact resolve eq126216 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq126216
  have eq126269 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq126217 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq126217 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq126217 eq16
    | (have j1 := eq126217 (τ X1) X0
       grind)
    | exact resolve eq16 eq126217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq126270 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq126217 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq126217 X0 (σ X0)
       grind)
    | exact superpose eq126217 eq9
    | (have j1 := eq126217 X1 X0
       grind)
    | exact resolve eq9 eq126217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126217
  have eq126307 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq126269 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq126269
    | (have j0 := eq126269 X0 X1
       grind)
    | exact resolve eq126269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126269
  have eq126313 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126307 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126307
    | (have j0 := eq126307 X0 X1
       grind)
    | exact resolve eq126307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126307
  have eq126882 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq126270 (σ X0) X1
       grind)
    | exact superpose eq126270 eq13
    | (have j1 := eq126270 (σ X0) X1
       grind)
    | exact resolve eq13 eq126270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126270
  have eq126898 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126882 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq126882
    | (have j0 := eq126882 X0 X1
       grind)
    | exact resolve eq126882 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126882
  have eq128001 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126898 x y
       grind)
    | exact superpose eq126898 eq14
    | (have j1 := eq126898 x y
       grind)
    | exact resolve eq14 eq126898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128140 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq128001
       have i₂ := eq7446
       grind)
    | exact superpose eq7446 eq128001
    | exact resolve eq128001 eq7446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7446 eq128001
  have eq128199 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq128140
       have i₂ := eq7624
       grind)
    | exact superpose eq7624 eq128140
    | (have r₁ := eq128140
       have r₂ := eq7624
       grind)
    | exact resolve eq128140 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq128202 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq128199
  have eq128328 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq128202
       grind)
    | exact superpose eq128202 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq128202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128352 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq126313 y y
       have i₂ := eq128202
       grind)
    | exact superpose eq128202 eq126313
    | exact resolve eq126313 eq128202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128202
  have eq128357 : x = (M.op y y) ∨ x = y := by grind
  clear eq128352
  have eq128373 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq128328
  have eq129103 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq128373
  have eq129122 : x = (M.op y y) := by
    first
    | (have r₁ := eq129103
       have r₂ := eq128357
       grind)
    | exact resolve eq129103 eq128357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128357 eq129103
  have eq129207 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq8
    | exact resolve eq8 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129210 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq18
    | exact resolve eq18 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq129263 : ∀ X0 X1 : G, (M.op x X0) ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq221 y X0 X1
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq221
    | (have j0 := eq221 X0 X0 X1
       grind)
    | exact resolve eq221 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq129374 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80556 y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq80556
    | (have j0 := eq80556 y
       grind)
    | exact resolve eq80556 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80556
  have eq129392 : y = (k (k y y) y) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq119588 y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq119588
    | (have j0 := eq119588 y
       grind)
    | exact resolve eq119588 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119588
  have eq129401 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq87 y y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq87
    | (have j0 := eq87 y y
       grind)
    | exact resolve eq87 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq129523 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op x (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq129207 (σ X0)
       have i₂ := eq126898 X0 X0
       grind)
    | exact superpose eq126898 eq129207
    | (have j1 := eq126898 X0 X0
       grind)
    | exact resolve eq129207 eq126898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129548 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq129207 y
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq129207
    | exact resolve eq129207 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129661 : ∀ X0 X1 : G, (M.op x X0) = (M.op (k X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7612 X1 X0
       have i₂ := eq129207 X0
       grind)
    | exact superpose eq129207 eq7612
    | (have j0 := eq7612 X1 X1
       grind)
    | exact resolve eq7612 eq129207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7612
  have eq129668 : ∀ X0 X1 : G, (M.op x X0) = (M.op (k X1 X1) X0) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90514 X1 X0
       have i₂ := eq129207 X0
       grind)
    | exact superpose eq129207 eq90514
    | (have j0 := eq90514 X1 X1
       grind)
    | exact resolve eq90514 eq129207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90514
  have eq129915 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq80528 y x
       have i₂ := eq129548
       grind)
    | exact superpose eq129548 eq80528
    | (have j0 := eq80528 y x
       grind)
    | exact resolve eq80528 eq129548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80528
  have eq130027 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op x X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129210 (σ X0) X1
       have i₂ := eq126898 X0 X0
       grind)
    | exact superpose eq126898 eq129210
    | (have j1 := eq126898 X0 X0
       grind)
    | exact resolve eq129210 eq126898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130048 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op x X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq129210 (τ X0) X1
       have i₂ := eq6358 X0
       grind)
    | exact superpose eq6358 eq129210
    | (have j1 := eq6358 X0
       grind)
    | exact resolve eq129210 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137939 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k (M.op X0 X0) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq129263 (M.op x x) X0
       have i₂ := eq129207 x
       grind)
    | exact superpose eq129207 eq129263
    | (have j0 := eq129263 (M.op x x) X0
       grind)
    | (have r₁ := eq129263 (M.op x x) x
       have r₂ := eq129207 x
       grind)
    | exact resolve eq129263 eq129207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129207 eq129263
  have eq137940 : ∀ X0 : G, (M.op x x) = (k (M.op X0 X0) (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq137939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137939
  have eq138185 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by
    first
    | (have i₁ := eq969 (M.op x x)
       have i₂ := eq137940 x
       grind)
    | exact superpose eq137940 eq969
    | (have j0 := eq969 (M.op x x)
       grind)
    | exact resolve eq969 eq137940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq138223 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by grind
  clear eq138185
  have eq162040 : (σ y) = (σ (M.op (k y y) y)) ∨ (M.op y y) = (k y y) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1083 (k y y) y
       have i₂ := eq129392
       grind)
    | exact superpose eq129392 eq1083
    | (have j0 := eq1083 (k y y) y
       grind)
    | exact resolve eq1083 eq129392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq129392
  have eq162053 : x = (k y y) ∨ (σ y) = (σ (M.op (k y y) y)) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq162040
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq162040
    | exact resolve eq162040 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162040
  have eq162071 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ (σ y) = (σ (M.op (k y y) y)) := by
    first
    | (have i₁ := eq162053
       have i₂ := eq129548
       grind)
    | exact superpose eq129548 eq162053
    | exact resolve eq162053 eq129548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162053
  have eq162077 : (σ y) = (σ (M.op (k y y) y)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq162071
       have r₂ := eq128140
       grind)
    | exact resolve eq162071 eq128140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162071
  have eq164612 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq162077
       have i₂ := eq129661 y y
       grind)
    | exact superpose eq129661 eq162077
    | (have j1 := eq129661 x y
       grind)
    | exact resolve eq162077 eq129661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129661
  have eq164613 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq162077
       have i₂ := eq129668 y y
       grind)
    | exact superpose eq129668 eq162077
    | (have j1 := eq129668 x y
       grind)
    | exact resolve eq162077 eq129668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129668 eq162077
  have eq164632 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq164613
       have r₂ := eq128140
       grind)
    | exact resolve eq164613 eq128140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164613
  have eq164633 : x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq164612
       have r₂ := eq128140
       grind)
    | exact resolve eq164612 eq128140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128140 eq164612
  have eq164638 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq164633
       have i₂ := eq129122
       grind)
    | exact superpose eq129122 eq164633
    | exact resolve eq164633 eq129122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164633
  have eq165018 : x ≠ y ∨ x = (k y y) := by grind
  clear eq164632
  have eq165044 : x = (k y y) := by
    first
    | (have r₁ := eq165018
       have r₂ := eq164638
       grind)
    | exact resolve eq165018 eq164638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164638 eq165018
  have eq167281 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) x) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq138223
       have i₂ := eq2614 x x
       grind)
    | (have i₁ := eq138223
       have i₂ := eq2614 X0 (τ (M.op x x))
       grind)
    | exact superpose eq2614 eq138223
    | (have j1 := eq2614 x X0
       grind)
    | exact resolve eq138223 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614 eq138223
  have eq171590 : ∀ X0 : G, (σ (τ X0)) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq69688 X0
       have i₂ := eq167281 (τ X0)
       grind)
    | exact superpose eq167281 eq69688
    | (have j0 := eq69688 X0
       have j1 := eq167281 (τ X0)
       grind)
    | exact resolve eq69688 eq167281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69688 eq167281
  have eq171614 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have j0 := eq171590 X0
       grind)
    | (have r₁ := eq171590 X0
       have r₂ := eq10 X0
       grind)
    | exact resolve eq171590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171590
  have eq171645 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq171614 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq171614
    | (have j0 := eq171614 X0
       grind)
    | exact resolve eq171614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171614
  have eq171970 : x = y ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq165044
       have i₂ := eq171645 y
       grind)
    | exact superpose eq171645 eq165044
    | (have j1 := eq171645 y
       grind)
    | exact resolve eq165044 eq171645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171645
  have eq172005 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq171970
       have i₂ := eq129548
       grind)
    | exact superpose eq129548 eq171970
    | exact resolve eq171970 eq129548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129548 eq171970
  have eq179082 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130027 y x
       have i₂ := eq165044
       grind)
    | exact superpose eq165044 eq130027
    | exact resolve eq130027 eq165044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130027
  have eq179244 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq179082 (σ y)
       grind)
    | exact superpose eq179082 eq14
    | exact resolve eq14 eq179082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179082
  have eq180955 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6358 X0
       have i₂ := eq130048 X0 (τ X0)
       grind)
    | exact superpose eq130048 eq6358
    | (have j0 := eq6358 X0
       have j1 := eq130048 X0 x
       grind)
    | exact resolve eq6358 eq130048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358 eq130048
  have eq181085 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq180955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180955
  have eq181371 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (σ X0)) = (M.op x (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181085 (σ X0)
       grind)
    | exact superpose eq181085 eq13
    | (have j1 := eq181085 (σ X0)
       grind)
    | exact resolve eq13 eq181085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181085
  have eq181385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq181371 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq181371
    | (have j0 := eq181371 X0
       grind)
    | exact resolve eq181371 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181371
  have eq190092 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op x X1) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129210 (σ X0) X1
       have i₂ := eq181385 X0
       grind)
    | exact superpose eq181385 eq129210
    | (have j1 := eq181385 X0
       grind)
    | exact resolve eq129210 eq181385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129210 eq181385
  have eq192506 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq190092 y X0
       have i₂ := eq165044
       grind)
    | exact superpose eq165044 eq190092
    | (have j0 := eq190092 y x
       grind)
    | exact resolve eq190092 eq165044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190092
  have eq192653 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq192506 (σ y)
       grind)
    | exact superpose eq192506 eq14
    | exact resolve eq14 eq192506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192506
  have eq241201 : (M.op (σ y) (σ x)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq129523 y
       have i₂ := eq165044
       grind)
    | exact superpose eq165044 eq129523
    | exact resolve eq129523 eq165044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129523
  have eq241225 : (σ (k y x)) = (M.op x (σ y)) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq374 y x
       have i₂ := eq241201
       grind)
    | exact superpose eq241201 eq374
    | (have j0 := eq374 y x
       grind)
    | exact resolve eq374 eq241201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq241230 : (σ (k y x)) = (M.op x (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq126898 y x
       have i₂ := eq241201
       grind)
    | exact superpose eq241201 eq126898
    | (have j0 := eq126898 y x
       grind)
    | exact resolve eq126898 eq241201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126898 eq241201
  have eq253878 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq241225
       have i₂ := eq172005
       grind)
    | exact superpose eq172005 eq241225
    | exact resolve eq241225 eq172005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172005 eq241225
  have eq253880 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq253878
  have eq253881 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq253880
       have r₂ := eq179244
       grind)
    | exact resolve eq253880 eq179244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179244 eq253880
  have eq253909 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq129915
       have i₂ := eq253881
       grind)
    | exact superpose eq253881 eq129915
    | exact resolve eq129915 eq253881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129915
  have eq253926 : (σ x) ≠ (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq192653
       have i₂ := eq253881
       grind)
    | exact superpose eq253881 eq192653
    | exact resolve eq192653 eq253881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192653 eq253881
  have eq254061 : (σ x) ≠ (M.op x (σ y)) ∨ x = y := by grind
  clear eq253926
  have eq254069 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq253909
  have eq262536 : (σ x) = (M.op x (σ y)) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq254069
       have i₂ := eq241230
       grind)
    | exact superpose eq241230 eq254069
    | exact resolve eq254069 eq241230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241230 eq254069
  have eq262538 : (σ x) = (M.op x (σ y)) ∨ x = y ∨ y = (k x x) := by grind
  clear eq262536
  have eq262541 : y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq262538
       have r₂ := eq254061
       grind)
    | exact resolve eq262538 eq254061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254061 eq262538
  have eq263092 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq126313 x x
       have i₂ := eq262541
       grind)
    | exact superpose eq262541 eq126313
    | exact resolve eq126313 eq262541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126313 eq262541
  have eq263109 : y = (M.op x x) ∨ x = y := by grind
  clear eq263092
  have eq263746 : y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq137940 x
       have i₂ := eq263109
       grind)
    | exact superpose eq263109 eq137940
    | exact resolve eq137940 eq263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137940 eq263109
  have eq263915 : y = (k y y) := by
    first
    | (have r₁ := eq263746
       have r₂ := eq129401
       grind)
    | exact resolve eq263746 eq129401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129401 eq263746
  have eq263989 : x = y := by
    first
    | (have i₁ := eq263915
       have i₂ := eq165044
       grind)
    | exact superpose eq165044 eq263915
    | exact resolve eq263915 eq165044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165044 eq263915
  have eq264027 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263989
       grind)
    | exact superpose eq263989 eq14
    | exact resolve eq14 eq263989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264097 : x = (M.op x x) := by
    first
    | (have i₁ := eq129122
       have i₂ := eq263989
       grind)
    | exact superpose eq263989 eq129122
    | exact resolve eq129122 eq263989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129122
  have eq264117 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq129374
       have i₂ := eq263989
       grind)
    | exact superpose eq263989 eq129374
    | exact resolve eq129374 eq263989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129374 eq263989
  have eq264399 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq264117
  have eq264449 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq264027
       have i₂ := eq264097
       grind)
    | exact superpose eq264097 eq264027
    | exact resolve eq264027 eq264097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264027 eq264097
  have eq264467 : False := by grind
  exact eq264467

/-- `Equation439`: `x = x ◇ (y ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation439 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law439 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law439.models_iff G M).mp hM
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq77 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq77 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq77 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq81 (σ X0) (σ X1)
       grind)
    | exact superpose eq81 eq13
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq97
    | exact resolve eq97 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq97
  have eq1046 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102 x y
       grind)
    | exact superpose eq102 eq14
    | (have r₁ := eq14
       have r₂ := eq102 x y
       grind)
    | exact resolve eq14 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1067 : False := by grind
  exact eq1067

/-- `Equation439`: `x = x ◇ (y ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation439 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law439 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law439.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq36 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq25 (τ X0) X1
       grind)
    | exact superpose eq25 eq17
    | (have j1 := eq25 (τ X0) X1
       grind)
    | exact resolve eq17 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq83 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq41
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq97 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq20
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq20 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq97
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq97 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq97
  have eq239 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq221
    | (have j0 := eq221 X0 X1
       grind)
    | exact resolve eq221 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq573 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq573
    | (have j0 := eq573 X0 X1
       grind)
    | exact resolve eq573 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq671 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq716 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq770 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1
       have i₂ := eq647 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq647 (M.op X0 X0) X1
       grind)
    | exact superpose eq647 eq20
    | (have j1 := eq647 X0 X1
       grind)
    | exact resolve eq20 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1139 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq20
    | (have j1 := eq53 X0 X0
       grind)
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53
  have eq1739 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq196 x y
       grind)
    | exact superpose eq196 eq14
    | (have j1 := eq196 x y
       grind)
    | exact resolve eq14 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq5622 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1760 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1760
    | (have j0 := eq1760 (τ X1) (τ X0)
       grind)
    | exact resolve eq1760 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq5651 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5622 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5622
    | (have j0 := eq5622 X0 X1
       grind)
    | exact resolve eq5622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5622
  have eq5659 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5651 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5651
    | (have j0 := eq5651 X0 X1
       grind)
    | exact resolve eq5651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq5662 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5659 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5659
    | (have j0 := eq5659 X0 X1
       grind)
    | exact resolve eq5659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5663 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5662 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5662
    | (have j0 := eq5662 X0 X1
       grind)
    | exact resolve eq5662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5662
  have eq8832 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq239 x y
       grind)
    | exact superpose eq239 eq14
    | (have j1 := eq239 x y
       grind)
    | exact resolve eq14 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq8870 : y = (k y x) := by
    first
    | (have j1 := eq716 x y
       grind)
    | (have r₁ := eq8832
       have r₂ := eq716 x y
       grind)
    | exact resolve eq8832 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq8832
  have eq9011 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq24
    | (have j0 := eq24 x y
       grind)
    | exact resolve eq24 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq9014 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq770 x y
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq770
    | (have j0 := eq770 x y
       grind)
    | exact resolve eq770 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9015 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1760 x y
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq1760
    | (have j0 := eq1760 x y
       grind)
    | exact resolve eq1760 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9016 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5663 y x
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq5663
    | (have j0 := eq5663 y x
       grind)
    | exact resolve eq5663 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8870
  have eq9372 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq9011
       grind)
    | exact superpose eq9011 eq8
    | exact resolve eq8 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12110 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9372
       have i₂ := eq9011
       grind)
    | exact superpose eq9011 eq9372
    | exact resolve eq9372 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9372
  have eq12127 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12110
       have r₂ := eq9016
       grind)
    | exact resolve eq12110 eq9016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12110
  have eq12282 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12127
       have i₂ := eq9011
       grind)
    | exact superpose eq9011 eq12127
    | exact resolve eq12127 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9011 eq12127
  have eq12299 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12282
       have r₂ := eq9016
       grind)
    | exact resolve eq12282 eq9016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9016 eq12282
  have eq13059 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 y y
       have i₂ := eq12299
       grind)
    | exact superpose eq12299 eq59
    | (have j0 := eq59 y y
       grind)
    | (have r₁ := eq59 y y
       have r₂ := eq12299
       grind)
    | exact resolve eq59 eq12299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq12299
  have eq13071 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq13059
  have eq13246 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1760 y y
       have i₂ := eq13071
       grind)
    | exact superpose eq13071 eq1760
    | (have j0 := eq1760 y y
       grind)
    | exact resolve eq1760 eq13071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq13071
  have eq13249 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13246
  have eq19569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1739
       have i₂ := eq647 x y
       grind)
    | exact superpose eq647 eq1739
    | (have j1 := eq647 x y
       grind)
    | (have r₁ := eq1739
       have r₂ := eq647 x y
       grind)
    | exact resolve eq1739 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq19571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1739
       have i₂ := eq770 x y
       grind)
    | exact superpose eq770 eq1739
    | (have j1 := eq770 (σ x) (σ y)
       grind)
    | (have r₁ := eq1739
       have r₂ := eq770 x y
       grind)
    | exact resolve eq1739 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1739
  have eq19575 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19571
  have eq19577 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19569
  have eq19594 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19577
       grind)
    | exact superpose eq19577 eq14
    | exact resolve eq14 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq20202 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19575
       grind)
    | exact superpose eq19575 eq14
    | exact resolve eq14 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20216 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85 (σ x) y
       have i₂ := eq19575
       grind)
    | exact superpose eq19575 eq85
    | (have j0 := eq85 (σ x) y
       grind)
    | exact resolve eq85 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq19575
  have eq20248 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20216
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq20216
    | exact resolve eq20216 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20216
  have eq20266 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5663 y x
       grind)
    | (have r₁ := eq20248
       have r₂ := eq5663 y x
       grind)
    | exact resolve eq20248 eq5663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5663 eq20248
  have eq20676 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20202
       have i₂ := eq9014
       grind)
    | exact superpose eq9014 eq20202
    | exact resolve eq20202 eq9014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014 eq20202
  have eq20679 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq20676
  have eq21360 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13249
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq13249
    | exact resolve eq13249 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13249 eq20266
  have eq21444 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq21360
  have eq21479 : x = (M.op x y) := by
    first
    | (have r₁ := eq21444
       have r₂ := eq20679
       grind)
    | exact resolve eq21444 eq20679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20679 eq21444
  have eq21640 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19594
       have i₂ := eq21479
       grind)
    | exact superpose eq21479 eq19594
    | exact resolve eq19594 eq21479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19594
  have eq21661 : x = (M.op y y) := by grind
  clear eq21640
  have eq21908 : y = (M.op y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq8
    | exact resolve eq8 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21910 : y = (M.op y (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq26
    | exact resolve eq26 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28151 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq21908
       have i₂ := eq21910
       grind)
    | exact superpose eq21910 eq21908
    | exact resolve eq21908 eq21910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21908 eq21910
  have eq28212 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq28151
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq28151
    | exact resolve eq28151 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28151
  have eq28746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1139 y
       have i₂ := eq28212
       grind)
    | exact superpose eq28212 eq1139
    | exact resolve eq1139 eq28212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139 eq28212
  have eq28787 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq28746
       have r₂ := eq9015
       grind)
    | exact resolve eq28746 eq9015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28746
  have eq29407 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq28787
       grind)
    | exact superpose eq28787 eq14
    | exact resolve eq14 eq28787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28787
  have eq29464 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq29407
       have i₂ := eq21479
       grind)
    | exact superpose eq21479 eq29407
    | exact resolve eq29407 eq21479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479 eq29407
  have eq29465 : x = y := by grind
  clear eq29464
  have eq30056 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29465
       grind)
    | exact superpose eq29465 eq14
    | exact resolve eq14 eq29465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30064 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9015
       have i₂ := eq29465
       grind)
    | exact superpose eq29465 eq9015
    | exact resolve eq9015 eq29465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015
  have eq30096 : x = (M.op x x) := by
    first
    | (have i₁ := eq21661
       have i₂ := eq29465
       grind)
    | exact superpose eq29465 eq21661
    | exact resolve eq21661 eq29465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21661 eq29465
  have eq30117 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30064
  have eq30122 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30056
       have i₂ := eq30096
       grind)
    | exact superpose eq30096 eq30056
    | exact resolve eq30056 eq30096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30056 eq30096
  have eq30123 : False := by grind
  exact eq30123

/-- `Equation439`: `x = x ◇ (y ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation439 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law439 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law439.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq32
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq54 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 (τ X0) X1
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 (τ X0) X1
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq20
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq20 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq54
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq54
  have eq242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq578 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq652 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq676 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq60
    | exact resolve eq60 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq721 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq775 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1
       have i₂ := eq652 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq652 (M.op X0 X0) X1
       grind)
    | exact superpose eq652 eq20
    | (have j1 := eq652 X0 X1
       grind)
    | exact resolve eq20 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq20
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55
  have eq1749 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq14
    | (have j1 := eq198 x y
       grind)
    | exact resolve eq14 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq5274 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1770 (τ X0) (τ X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq1770
    | (have j0 := eq1770 (τ X0) (τ X1)
       grind)
    | exact resolve eq1770 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq5312 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5274 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5274
    | (have j0 := eq5274 X0 X1
       grind)
    | exact resolve eq5274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5274
  have eq5317 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5312 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5312
    | (have j0 := eq5312 X0 X1
       grind)
    | exact resolve eq5312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5312
  have eq5318 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5317 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5317
    | (have j0 := eq5317 X0 X1
       grind)
    | exact resolve eq5317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5317
  have eq5319 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5318 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5318
    | (have j0 := eq5318 X0 X1
       grind)
    | exact resolve eq5318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318
  have eq7471 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq242 x y
       grind)
    | exact superpose eq242 eq14
    | (have j1 := eq242 x y
       grind)
    | exact resolve eq14 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq7507 : y = (k x y) := by
    first
    | (have j1 := eq721 x y
       grind)
    | (have r₁ := eq7471
       have r₂ := eq721 x y
       grind)
    | exact resolve eq7471 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq7471
  have eq8095 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq7507
       grind)
    | exact superpose eq7507 eq24
    | (have j0 := eq24 x y
       grind)
    | exact resolve eq24 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8098 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq775 x y
       have i₂ := eq7507
       grind)
    | exact superpose eq7507 eq775
    | (have j0 := eq775 x y
       grind)
    | exact resolve eq775 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8099 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1770 x y
       have i₂ := eq7507
       grind)
    | exact superpose eq7507 eq1770
    | (have j0 := eq1770 x y
       grind)
    | exact resolve eq1770 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8100 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5319 x y
       have i₂ := eq7507
       grind)
    | exact superpose eq7507 eq5319
    | (have j0 := eq5319 x y
       grind)
    | exact resolve eq5319 eq7507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507
  have eq8891 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq8
    | exact resolve eq8 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11611 : y = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8891
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq8891
    | exact resolve eq8891 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8891
  have eq11628 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11611
       have r₂ := eq8100
       grind)
    | exact resolve eq11611 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11611
  have eq11750 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11628
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq11628
    | exact resolve eq11628 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095 eq11628
  have eq11767 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11750
       have r₂ := eq8100
       grind)
    | exact resolve eq11750 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100 eq11750
  have eq11951 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 y y
       have i₂ := eq11767
       grind)
    | exact superpose eq11767 eq61
    | (have j0 := eq61 y y
       grind)
    | (have r₁ := eq61 y y
       have r₂ := eq11767
       grind)
    | exact resolve eq61 eq11767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq11767
  have eq11963 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq11951
  have eq12148 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1770 y y
       have i₂ := eq11963
       grind)
    | exact superpose eq11963 eq1770
    | (have j0 := eq1770 y y
       grind)
    | exact resolve eq1770 eq11963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq11963
  have eq12151 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12148
  have eq19516 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1749
       have i₂ := eq652 x y
       grind)
    | exact superpose eq652 eq1749
    | (have j1 := eq652 x y
       grind)
    | (have r₁ := eq1749
       have r₂ := eq652 x y
       grind)
    | exact resolve eq1749 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq19518 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1749
       have i₂ := eq775 x y
       grind)
    | exact superpose eq775 eq1749
    | (have j1 := eq775 (σ x) (σ y)
       grind)
    | (have r₁ := eq1749
       have r₂ := eq775 x y
       grind)
    | exact resolve eq1749 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq1749
  have eq19522 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19518
  have eq19524 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq19516
  have eq19541 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19524
       grind)
    | exact superpose eq19524 eq14
    | exact resolve eq14 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524
  have eq20173 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19522
       grind)
    | exact superpose eq19522 eq14
    | exact resolve eq14 eq19522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20188 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49 (σ x) y
       have i₂ := eq19522
       grind)
    | exact superpose eq19522 eq49
    | (have j0 := eq49 (σ x) y
       grind)
    | exact resolve eq49 eq19522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq19522
  have eq20218 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20188
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq20188
    | exact resolve eq20188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20188
  have eq20236 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5319 x y
       grind)
    | (have r₁ := eq20218
       have r₂ := eq5319 x y
       grind)
    | exact resolve eq20218 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319 eq20218
  have eq20656 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20173
       have i₂ := eq8098
       grind)
    | exact superpose eq8098 eq20173
    | exact resolve eq20173 eq8098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098 eq20173
  have eq20659 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq20656
  have eq21361 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12151
       have i₂ := eq20236
       grind)
    | exact superpose eq20236 eq12151
    | exact resolve eq12151 eq20236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12151 eq20236
  have eq21444 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq21361
  have eq21478 : x = (M.op x y) := by
    first
    | (have r₁ := eq21444
       have r₂ := eq20659
       grind)
    | exact resolve eq21444 eq20659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20659 eq21444
  have eq21640 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19541
       have i₂ := eq21478
       grind)
    | exact superpose eq21478 eq19541
    | exact resolve eq19541 eq21478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541
  have eq21661 : x = (M.op y y) := by grind
  clear eq21640
  have eq21898 : y = (M.op y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq8
    | exact resolve eq8 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21900 : y = (M.op y (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq26
    | exact resolve eq26 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq27469 : y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq21898
       have i₂ := eq21900
       grind)
    | exact superpose eq21900 eq21898
    | exact resolve eq21898 eq21900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21898 eq21900
  have eq27530 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq27469
       have i₂ := eq21661
       grind)
    | exact superpose eq21661 eq27469
    | exact resolve eq27469 eq21661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27469
  have eq28210 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1145 y
       have i₂ := eq27530
       grind)
    | exact superpose eq27530 eq1145
    | exact resolve eq1145 eq27530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq27530
  have eq28252 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq28210
       have r₂ := eq8099
       grind)
    | exact resolve eq28210 eq8099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28210
  have eq28869 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq28252
       grind)
    | exact superpose eq28252 eq14
    | exact resolve eq14 eq28252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28252
  have eq28926 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq28869
       have i₂ := eq21478
       grind)
    | exact superpose eq21478 eq28869
    | exact resolve eq28869 eq21478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21478 eq28869
  have eq28927 : x = y := by grind
  clear eq28926
  have eq29609 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28927
       grind)
    | exact superpose eq28927 eq14
    | exact resolve eq14 eq28927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29617 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8099
       have i₂ := eq28927
       grind)
    | exact superpose eq28927 eq8099
    | exact resolve eq8099 eq28927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8099
  have eq29648 : x = (M.op x x) := by
    first
    | (have i₁ := eq21661
       have i₂ := eq28927
       grind)
    | exact superpose eq28927 eq21661
    | exact resolve eq21661 eq28927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21661 eq28927
  have eq29667 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29617
  have eq29672 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29609
       have i₂ := eq29648
       grind)
    | exact superpose eq29648 eq29609
    | exact resolve eq29609 eq29648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29609 eq29648
  have eq29673 : False := by grind
  exact eq29673

/-- `Equation4391`: `x ◇ (x ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4391 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4391 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4391.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq18 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq182 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq167 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq167
    | exact resolve eq167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq236 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X4) ∨ (M.op X3 X4) = (k (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq91 (M.op X3 X4) X2
       have i₂ := eq18 X3 X4 X2 X0 X1
       grind)
    | (have i₁ := eq91 (M.op X3 X4) X2
       have i₂ := eq18 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq18 eq91
    | (have j0 := eq91 (M.op X3 X4) X2
       grind)
    | (have r₁ := eq91 (M.op (M.op X3 X4) X2) X2
       have r₂ := eq18 (M.op X3 X4) X2 X2 X3 X4
       grind)
    | (have r₁ := eq91 (M.op (M.op X0 X1) X2) X2
       have r₂ := eq18 X0 X1 X2 (M.op X0 X1) X2
       grind)
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq182 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq182
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq757 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq757 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq757
    | (have j0 := eq757 X0
       grind)
    | exact resolve eq757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq762 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq759 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq759
    | (have j0 := eq759 X0
       grind)
    | exact resolve eq759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq774 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq762 (τ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq762
    | (have j0 := eq762 (τ X0)
       grind)
    | exact resolve eq762 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq798 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq798
    | (have j0 := eq798 X0 X1
       grind)
    | exact resolve eq798 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq940 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1796 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1800 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (M.op X1 X2) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) X1 X2
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq8
    | (have j1 := eq85 X0 X0
       grind)
    | exact resolve eq8 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1801 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq85 X0 X0
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq353
       have i₂ := eq940 y x
       grind)
    | exact superpose eq940 eq353
    | (have j1 := eq940 y x
       grind)
    | (have r₁ := eq353
       have r₂ := eq940 y x
       grind)
    | exact resolve eq353 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq2058 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq353
       have i₂ := eq876 y x
       grind)
    | exact superpose eq876 eq353
    | (have j1 := eq876 (σ y) (σ x)
       grind)
    | (have r₁ := eq353
       have r₂ := eq876 y x
       grind)
    | exact resolve eq353 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq2059 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2058
  have eq2060 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2057
  have eq2070 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq182
    | exact resolve eq182 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2093 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2070
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2070
    | exact resolve eq2070 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2175 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2093
       grind)
    | exact superpose eq2093 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq876 y x
       have i₂ := eq2093
       grind)
    | exact superpose eq2093 eq876
    | (have j0 := eq876 y x
       grind)
    | exact resolve eq876 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq2093
  have eq2179 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2178
  have eq2180 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2175
  have eq2230 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq367 x x
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq367
    | exact resolve eq367 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2270 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2230
    | exact resolve eq2230 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2280 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq2180
       grind)
    | exact superpose eq2180 eq8
    | exact resolve eq8 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2282 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x y
       have i₂ := eq2180
       grind)
    | exact superpose eq2180 eq18
    | exact resolve eq18 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3104 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq2060
       grind)
    | exact superpose eq2060 eq182
    | exact resolve eq182 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq2060
  have eq3134 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3104
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3104
    | exact resolve eq3104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq3135 : x = (k x y) := by grind
  clear eq3134
  have eq3757 : (M.op (σ x) (σ y)) = (M.op x (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2280 (σ x)
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq2280
    | exact resolve eq2280 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq3810 : (M.op (σ x) (σ y)) = (M.op x (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3757
  have eq20083 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq774 (σ X0)
       have i₂ := eq301 (σ X0) X0
       grind)
    | exact superpose eq301 eq774
    | (have j0 := eq774 (σ X0)
       have j1 := eq301 (σ X0) X0
       grind)
    | exact resolve eq774 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq774
  have eq20110 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20083 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20083
    | (have j0 := eq20083 X0
       grind)
    | exact resolve eq20083 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20083
  have eq20119 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20110 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20110
    | (have j0 := eq20110 X0
       grind)
    | exact resolve eq20110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20110
  have eq20121 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq20119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20119
    | (have j0 := eq20119 X0
       grind)
    | exact resolve eq20119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119
  have eq20123 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq20121 X0
       have j1 := eq91 X0 X0
       grind)
    | (have r₁ := eq20121 x
       have r₂ := eq91 x x
       grind)
    | exact resolve eq20121 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq20121
  have eq20814 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20123 x
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq20123
    | (have j0 := eq20123 x
       grind)
    | exact resolve eq20123 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123
  have eq20839 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20814
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq20814
    | exact resolve eq20814 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20814
  have eq29854 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2270
       grind)
    | exact superpose eq2270 eq9
    | exact resolve eq9 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq29950 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29854
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq29854
    | exact resolve eq29854 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29854
  have eq31550 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30 x x
       have i₂ := eq29950
       grind)
    | exact superpose eq29950 eq30
    | exact resolve eq30 eq29950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29950
  have eq31577 : y = (M.op x x) ∨ x = y := by grind
  clear eq31550
  have eq32773 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq31577
       grind)
    | exact superpose eq31577 eq8
    | exact resolve eq8 eq31577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32775 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x x
       have i₂ := eq31577
       grind)
    | exact superpose eq31577 eq18
    | exact resolve eq18 eq31577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33809 : (M.op x y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq32773 x
       have i₂ := eq31577
       grind)
    | exact superpose eq31577 eq32773
    | exact resolve eq32773 eq31577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31577
  have eq34004 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq33809
  have eq52483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq236 X0 X1 X2 (M.op X0 X1) X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq52571 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52483 X0 x x
       have i₂ := eq32775 X0 x x
       grind)
    | exact superpose eq32775 eq52483
    | exact resolve eq52483 eq32775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32775
  have eq52654 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq52571 x
       have i₂ := eq34004
       grind)
    | exact superpose eq34004 eq52571
    | exact resolve eq52571 eq34004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34004
  have eq52664 : (M.op y y) = (k (M.op y y) (M.op y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq52571 (M.op y y)
       have i₂ := eq32773 y
       grind)
    | exact superpose eq32773 eq52571
    | exact resolve eq52571 eq32773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32773 eq52571
  have eq52696 : (M.op y y) = (k (M.op y y) (M.op y y)) ∨ x = y := by grind
  clear eq52664
  have eq52697 : (M.op x y) = (k (M.op x y) x) ∨ x = y := by grind
  clear eq52654
  have eq52758 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52697
       have i₂ := eq2180
       grind)
    | exact superpose eq2180 eq52697
    | exact resolve eq52697 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180 eq52697
  have eq52781 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq52758
       have r₂ := eq20839
       grind)
    | exact resolve eq52758 eq20839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20839 eq52758
  have eq52928 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq390 x
       have i₂ := eq52781
       grind)
    | exact superpose eq52781 eq390
    | (have j0 := eq390 x
       grind)
    | exact resolve eq390 eq52781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52945 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq52781
       grind)
    | exact superpose eq52781 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq52781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52781
  have eq52961 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq52945
  have eq52968 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq52928
  have eq53134 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq52961
       grind)
    | exact superpose eq52961 eq8
    | exact resolve eq8 eq52961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53172 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq52961
  have eq54512 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2059
       have i₂ := eq52968
       grind)
    | exact superpose eq52968 eq2059
    | exact resolve eq2059 eq52968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq54590 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2282 (σ x) (σ x) X0
       have i₂ := eq52968
       grind)
    | exact superpose eq52968 eq2282
    | exact resolve eq2282 eq52968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq54600 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq54590 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54590
  have eq54610 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq54512
  have eq54752 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq54610
       grind)
    | exact superpose eq54610 eq8
    | exact resolve eq8 eq54610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55444 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52968
       have i₂ := eq54600 (σ x)
       grind)
    | exact superpose eq54600 eq52968
    | exact resolve eq52968 eq54600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52968 eq54600
  have eq55539 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x x) := by grind
  clear eq55444
  have eq56779 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq762 (M.op y y)
       have i₂ := eq52696
       grind)
    | exact superpose eq52696 eq762
    | (have j0 := eq762 (M.op y y)
       grind)
    | (have r₁ := eq762 (M.op y y)
       have r₂ := eq52696
       grind)
    | exact resolve eq762 eq52696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq52696
  have eq56784 : (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ x = y := by grind
  clear eq56779
  have eq56934 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op X0 X1) (M.op y y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 (M.op y y) y y
       have i₂ := eq56784
       grind)
    | exact superpose eq56784 eq18
    | exact resolve eq18 eq56784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56784
  have eq57480 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) (M.op y y)) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56934 X0 (M.op X0 X0)
       have i₂ := eq53134 X0
       grind)
    | exact superpose eq53134 eq56934
    | (have j0 := eq56934 y X0
       grind)
    | exact resolve eq56934 eq53134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53134 eq56934
  have eq57505 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) (M.op y y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq57480 X0
       grind)
    | (have r₁ := eq57480 X0
       have r₂ := eq53172
       grind)
    | exact resolve eq57480 eq53172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53172 eq57480
  have eq58886 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54752 x
       have i₂ := eq54610
       grind)
    | exact superpose eq54610 eq54752
    | exact resolve eq54752 eq54610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54610 eq54752
  have eq59027 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq58886
  have eq61076 : (σ (M.op x y)) ≠ (M.op x (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3810
       grind)
    | exact superpose eq3810 eq14
    | exact resolve eq14 eq3810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3810
  have eq61172 : (σ x) ≠ (M.op x (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61076
       have i₂ := eq2179
       grind)
    | exact superpose eq2179 eq61076
    | exact resolve eq61076 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179 eq61076
  have eq61173 : (σ x) ≠ (M.op x (σ x)) ∨ y = (M.op x x) := by grind
  clear eq61172
  have eq61175 : y = (M.op x x) := by
    first
    | (have r₁ := eq61173
       have r₂ := eq55539
       grind)
    | exact resolve eq61173 eq55539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55539 eq61173
  have eq61211 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq61175
       grind)
    | exact superpose eq61175 eq8
    | exact resolve eq8 eq61175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61213 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 x x
       have i₂ := eq61175
       grind)
    | exact superpose eq61175 eq18
    | exact resolve eq18 eq61175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61288 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq52483 x x x
       have i₂ := eq61175
       grind)
    | exact superpose eq61175 eq52483
    | exact resolve eq52483 eq61175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52483
  have eq62631 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq61288 (M.op y y)
       have i₂ := eq61211 y
       grind)
    | exact superpose eq61211 eq61288
    | exact resolve eq61288 eq61211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61211 eq61288
  have eq63248 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq390 (M.op y y)
       have i₂ := eq62631
       grind)
    | exact superpose eq62631 eq390
    | (have j0 := eq390 (M.op y y)
       grind)
    | exact resolve eq390 eq62631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63269 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
  clear eq63248
  have eq67461 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq67462 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq67461 X0 X1
       have j1 := eq338 X1 X0
       grind)
    | (have r₁ := eq67461 (k X1 X1) X0
       have r₂ := eq338 X0 X1
       grind)
    | (have r₁ := eq67461 X0 (σ (k X1 X1))
       have r₂ := eq338 (σ X0) X1
       grind)
    | (have r₁ := eq67461 X1 X0
       have r₂ := eq338 X0 X1
       grind)
    | exact resolve eq67461 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq67461
  have eq68453 : ∀ X0 : G, (τ (σ (M.op y y))) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq367 (M.op y y) X0
       have i₂ := eq63269
       grind)
    | exact superpose eq63269 eq367
    | (have j0 := eq367 (M.op y y) X0
       grind)
    | exact resolve eq367 eq63269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq68568 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq61213 (σ (M.op y y)) (σ (M.op y y)) X0
       have i₂ := eq63269
       grind)
    | exact superpose eq63269 eq61213
    | exact resolve eq61213 eq63269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68671 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68453 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq68453
    | (have j0 := eq68453 X0
       grind)
    | exact resolve eq68453 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68453
  have eq68715 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq68671 X0
       have i₂ := eq68568 (σ X0)
       grind)
    | exact superpose eq68568 eq68671
    | (have j0 := eq68671 X0
       grind)
    | exact resolve eq68671 eq68568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68568 eq68671
  have eq71123 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq67462 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq67462 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq67462 eq16
    | (have j1 := eq67462 (τ X1) X0
       grind)
    | exact resolve eq16 eq67462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq71124 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq67462 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq67462 X0 (σ X0)
       grind)
    | exact superpose eq67462 eq9
    | (have j1 := eq67462 X1 X0
       grind)
    | exact resolve eq9 eq67462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67462
  have eq71144 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq71123 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq71123
    | (have j0 := eq71123 X0 X1
       grind)
    | exact resolve eq71123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71123
  have eq71154 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq71144 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71144
    | (have j0 := eq71144 X0 X1
       grind)
    | exact resolve eq71144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71144
  have eq71364 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq71154 (τ X1) X0
       grind)
    | exact superpose eq71154 eq17
    | (have j1 := eq71154 (τ X1) X0
       grind)
    | exact resolve eq17 eq71154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq71405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1796
       have i₂ := eq71154 y x
       grind)
    | exact superpose eq71154 eq1796
    | (have j1 := eq71154 y x
       grind)
    | exact resolve eq1796 eq71154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq71154
  have eq71524 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq71405
  have eq74126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq71124 (σ X1) X0
       grind)
    | exact superpose eq71124 eq13
    | (have j1 := eq71124 (σ X1) X0
       grind)
    | exact resolve eq13 eq71124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71124
  have eq74132 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74126 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq74126
    | (have j0 := eq74126 X0 X1
       grind)
    | exact resolve eq74126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74126
  have eq75126 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74132 x y
       grind)
    | exact superpose eq74132 eq14
    | (have j1 := eq74132 x y
       grind)
    | exact resolve eq14 eq74132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74132
  have eq75189 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq75126
       have i₂ := eq3135
       grind)
    | exact superpose eq3135 eq75126
    | exact resolve eq75126 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135 eq75126
  have eq75211 : y = (k x x) := by
    first
    | (have r₁ := eq75189
       have r₂ := eq71524
       grind)
    | exact resolve eq75189 eq71524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71524 eq75189
  have eq75274 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq390 x
       have i₂ := eq75211
       grind)
    | exact superpose eq75211 eq390
    | (have j0 := eq390 x
       grind)
    | exact resolve eq390 eq75211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq75288 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X1) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1800 x X1 x
       have i₂ := eq75211
       grind)
    | exact superpose eq75211 eq1800
    | exact resolve eq1800 eq75211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800 eq75211
  have eq75373 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75288 x x
       have i₂ := eq61213 x x (σ x)
       grind)
    | exact superpose eq61213 eq75288
    | exact resolve eq75288 eq61213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75288
  have eq77402 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75373
       grind)
    | exact superpose eq75373 eq14
    | exact resolve eq14 eq75373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75373
  have eq95882 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71364 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq71364
    | exact resolve eq71364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71364
  have eq95917 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95882 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq95882
    | (have j0 := eq95882 X0 X1
       grind)
    | exact resolve eq95882 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95882
  have eq96019 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (σ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq62631
       have i₂ := eq95917 X0 (M.op y y)
       grind)
    | (have i₁ := eq62631
       have i₂ := eq95917 (k (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq95917 eq62631
    | (have j1 := eq95917 X0 (M.op y y)
       grind)
    | exact resolve eq62631 eq95917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62631 eq95917
  have eq96032 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq96019 X0
       have i₂ := eq61213 y y X0
       grind)
    | exact superpose eq61213 eq96019
    | (have j0 := eq96019 X0
       grind)
    | exact resolve eq96019 eq61213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61213 eq96019
  have eq102344 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq96032 X0
       have i₂ := eq68715 X0
       grind)
    | exact superpose eq68715 eq96032
    | (have j0 := eq96032 X0
       have j1 := eq68715 X0
       grind)
    | exact resolve eq96032 eq68715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68715 eq96032
  have eq102349 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq102344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102344
  have eq102358 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102349 x
       have i₂ := eq59027
       grind)
    | exact superpose eq59027 eq102349
    | (have j0 := eq102349 x
       grind)
    | exact resolve eq102349 eq59027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59027 eq102349
  have eq102415 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq102358
       have r₂ := eq77402
       grind)
    | exact resolve eq102358 eq77402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77402 eq102358
  have eq102445 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63269
       have i₂ := eq102415
       grind)
    | exact superpose eq102415 eq63269
    | exact resolve eq63269 eq102415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63269
  have eq102496 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57505 y
       have i₂ := eq102415
       grind)
    | exact superpose eq102415 eq57505
    | exact resolve eq57505 eq102415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57505 eq102415
  have eq102645 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq102496
  have eq102697 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102645
       have i₂ := eq61175
       grind)
    | exact superpose eq61175 eq102645
    | exact resolve eq102645 eq61175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102645
  have eq102698 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq102445
       have r₂ := eq75274
       grind)
    | exact resolve eq102445 eq75274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75274 eq102445
  have eq102828 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq102697
       grind)
    | exact superpose eq102697 eq9
    | exact resolve eq9 eq102697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102697
  have eq102968 : x = y ∨ x = y := by
    first
    | (have i₁ := eq102828
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq102828
    | exact resolve eq102828 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102828
  have eq102969 : x = y := by grind
  clear eq102968
  have eq102986 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102969
       grind)
    | exact superpose eq102969 eq14
    | exact resolve eq14 eq102969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103337 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq102986
       have i₂ := eq61175
       grind)
    | exact superpose eq61175 eq102986
    | exact resolve eq102986 eq61175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61175 eq102986
  have eq103398 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq103337
       have i₂ := eq102698
       grind)
    | exact superpose eq102698 eq103337
    | exact resolve eq103337 eq102698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102698 eq103337
  have eq103419 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103398
       have i₂ := eq102969
       grind)
    | exact superpose eq102969 eq103398
    | exact resolve eq103398 eq102969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102969 eq103398
  have eq103420 : False := by grind
  exact eq103420
