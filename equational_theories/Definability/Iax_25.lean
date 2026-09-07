import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- `Equation4391`: `x ◇ (x ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4391 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4391 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4391.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X1 X2) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X2) X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op (M.op X1 X2) X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 (M.op X1 X2)
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34
    | exact resolve eq34 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq86 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq28
    | exact resolve eq28 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) X2) X2) = X2 ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    grind
  clear eq27
  have eq163 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq17
    | exact resolve eq17 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq173
    | exact resolve eq173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq226 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (M.op X2 X2)) = (M.op (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq237 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k (M.op X3 X4) X2) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq93 (M.op X3 X4) X2
       have i₂ := eq18 X3 X4 X2 X0 X1
       grind)
    | (have i₁ := eq93 (M.op X3 X4) X2
       have i₂ := eq18 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq18 eq93
    | (have j0 := eq93 (M.op X0 X1) X2
       grind)
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | (have i₁ := eq86 X0
       have i₂ := eq12 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq12 eq86
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq86
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq86 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq795 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
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
  have eq797 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq795
    | (have j0 := eq795 X0
       grind)
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq800 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq797 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq797
    | (have j0 := eq797 X0
       grind)
    | exact resolve eq797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq812 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq800 (τ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq800
    | (have j0 := eq800 (τ X0)
       grind)
    | exact resolve eq800 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = X1 ∨ (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq43
    | (have j1 := eq32 X0 (τ X1)
       grind)
    | exact resolve eq43 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq900 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq897 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq897
    | (have j0 := eq897 X0 X1
       grind)
    | exact resolve eq897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq913 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq920 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq900
    | (have j0 := eq900 X0 X1
       grind)
    | exact resolve eq900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq975 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq1000 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq913 X0 (τ X1)
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq913 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq913 eq43
    | (have j1 := eq913 X0 (τ X1)
       grind)
    | exact resolve eq43 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1005 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1530 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq145 x x X0
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq145
    | (have j0 := eq145 X0 x X0
       grind)
    | exact resolve eq145 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1862 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq87 X0 X0
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq87 X0 X0
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2342 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq367
    | exact resolve eq367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq2393 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2342 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2342
    | (have j0 := eq2342 X0 X1
       grind)
    | exact resolve eq2342 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq3316 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq163 X1 (σ X0)
       grind)
    | exact superpose eq163 eq13
    | (have j1 := eq163 X1 (σ X0)
       grind)
    | exact resolve eq13 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3364 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3316 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3316
    | (have j0 := eq3316 X0 X1
       grind)
    | exact resolve eq3316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316
  have eq3538 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq3364 X0 (τ X1)
       grind)
    | exact superpose eq3364 eq16
    | (have j1 := eq3364 X0 (τ X1)
       grind)
    | exact resolve eq16 eq3364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq5020 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2393 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2393
    | (have j0 := eq2393 X1 (τ X0)
       grind)
    | exact resolve eq2393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5350 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq6364 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq800 (τ X0)
       have i₂ := eq302 X0 (τ X0)
       grind)
    | exact superpose eq302 eq800
    | (have j0 := eq800 (τ X0)
       have j1 := eq302 X0 (τ X0)
       grind)
    | (have r₁ := eq800 (τ X0)
       have r₂ := eq302 X0 (τ X0)
       grind)
    | exact resolve eq800 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq800
  have eq6395 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq6364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6364
  have eq6411 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6395 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6395
    | (have j0 := eq6395 X0
       grind)
    | exact resolve eq6395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395
  have eq7447 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq394 x y
       grind)
    | exact superpose eq394 eq14
    | (have j1 := eq394 x y
       grind)
    | exact resolve eq14 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7512 : y = (k x y) := by
    first
    | (have j1 := eq975 x y
       grind)
    | (have r₁ := eq7447
       have r₂ := eq975 x y
       grind)
    | exact resolve eq7447 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq7447
  have eq8038 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq913 x y
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq913
    | (have j0 := eq913 x y
       grind)
    | exact resolve eq913 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11702 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq338 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq338 X0 X1
       grind)
    | exact superpose eq338 eq9
    | (have j1 := eq338 X0 X1
       grind)
    | exact resolve eq9 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq11770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11702 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11702
    | (have j0 := eq11702 X0 X1
       grind)
    | exact resolve eq11702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq26397 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq26904 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26397 X0 X1
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq26397
    | (have j0 := eq26397 X0 X1
       grind)
    | exact resolve eq26397 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26397
  have eq28380 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ (k X0 (σ X1))) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1
       have i₂ := eq26904 X0 (σ X1)
       grind)
    | (have i₁ := eq86 X0
       have i₂ := eq26904 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq26904 eq86
    | (have j1 := eq26904 X0 (σ X1)
       grind)
    | exact resolve eq86 eq26904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq26904
  have eq28477 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28380 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq28380
    | (have j0 := eq28380 X0 X1
       grind)
    | exact resolve eq28380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28380
  have eq32549 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq857
    | (have j0 := eq857 X1 (σ X0)
       grind)
    | exact resolve eq857 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32741 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq857 X1 X0
       grind)
    | exact superpose eq857 eq9
    | (have j1 := eq857 X1 X0
       grind)
    | exact resolve eq9 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32849 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq857 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq32850 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq32849 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32849
    | (have j0 := eq32849 X0
       grind)
    | exact resolve eq32849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32849
  have eq32855 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32741 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq32741
    | (have j0 := eq32741 X0 X1
       grind)
    | exact resolve eq32741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32741
  have eq32894 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32549 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32549
    | (have j0 := eq32549 X0 X1
       grind)
    | exact resolve eq32549 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32549
  have eq33691 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32850 (σ X0)
       have i₂ := eq163 X0 (σ X0)
       grind)
    | exact superpose eq163 eq32850
    | (have j0 := eq32850 (σ X0)
       have j1 := eq163 X0 (σ X0)
       grind)
    | (have r₁ := eq32850 (σ X0)
       have r₂ := eq163 X0 (σ X0)
       grind)
    | exact resolve eq32850 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq33697 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq33691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33691
  have eq33699 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33697 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33697
    | (have j0 := eq33697 X0
       grind)
    | exact resolve eq33697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33697
  have eq33707 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq33699 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33699
    | (have j0 := eq33699 X0
       grind)
    | exact resolve eq33699 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33699
  have eq36531 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33707 X1
       have i₂ := eq913 X0 X1
       grind)
    | (have i₁ := eq33707 X0
       have i₂ := eq913 (M.op X0 X0) X1
       grind)
    | exact superpose eq913 eq33707
    | (have j1 := eq913 X0 X1
       grind)
    | exact resolve eq33707 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq33707
  have eq37616 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32855 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32855
    | (have j0 := eq32855 (σ X0) X1
       grind)
    | exact resolve eq32855 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32855
  have eq51056 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1005 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1005
    | (have j0 := eq1005 X1 (σ X0)
       grind)
    | exact resolve eq1005 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51056 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq51056
    | (have j0 := eq51056 X0 X1
       grind)
    | exact resolve eq51056 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51056
  have eq51387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51366 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq51366
    | (have j0 := eq51366 X0 X1
       grind)
    | exact resolve eq51366 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51366
  have eq78076 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq3538 (τ X0) X0
       grind)
    | exact superpose eq3538 eq390
    | (have j0 := eq390 (τ X0)
       have j1 := eq3538 (τ X0) X0
       grind)
    | exact resolve eq390 eq3538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq78160 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq78076 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78076
    | (have j0 := eq78076 X0
       grind)
    | exact resolve eq78076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78076
  have eq78187 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq78160 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78160
    | (have j0 := eq78160 X0
       grind)
    | exact resolve eq78160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78160
  have eq78200 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq78187 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78187
    | (have j0 := eq78187 X0
       grind)
    | exact resolve eq78187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78187
  have eq78209 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq78200 X0
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq78200 x
       have r₂ := eq93 x x
       grind)
    | exact resolve eq78200 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78200
  have eq82954 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28477 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28477
    | (have j0 := eq28477 X1 (τ X0)
       grind)
    | exact resolve eq28477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq83282 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82954 X0 X1
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq82954
    | (have j0 := eq82954 X0 X1
       grind)
    | exact resolve eq82954 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82954
  have eq83330 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83282 X0 X1
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq83282
    | (have j0 := eq83282 X0 X1
       grind)
    | exact resolve eq83282 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83282
  have eq85275 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq51387 X0 X0
       grind)
    | exact superpose eq51387 eq390
    | (have j0 := eq390 X0
       have j1 := eq51387 X0 X0
       grind)
    | (have r₁ := eq390 x
       have r₂ := eq51387 x x
       grind)
    | exact resolve eq390 eq51387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85463 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq51387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51387
  have eq85493 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85275 X0
       have j1 := eq390 X0
       grind)
    | (have r₁ := eq85275 X0
       have r₂ := eq390 X0
       grind)
    | exact resolve eq85275 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85275
  have eq119893 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83330 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83330
  have eq128813 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11770 x y
       grind)
    | exact superpose eq11770 eq14
    | (have j1 := eq11770 x y
       grind)
    | exact resolve eq14 eq11770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11770
  have eq128823 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq36531 x y
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 (k x y) (M.op x y)
       grind)
    | (have r₁ := eq128813
       have r₂ := eq36531 x y
       grind)
    | exact resolve eq128813 eq36531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36531 eq128813
  have eq132696 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq132697 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq132696 X0 X1
       have j1 := eq339 X1 X0
       grind)
    | (have r₁ := eq132696 (k X1 X1) X0
       have r₂ := eq339 X0 X1
       grind)
    | (have r₁ := eq132696 X0 (σ (k X1 X1))
       have r₂ := eq339 (σ X0) X1
       grind)
    | (have r₁ := eq132696 X1 X0
       have r₂ := eq339 X0 X1
       grind)
    | exact resolve eq132696 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq132696
  have eq132743 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq132697 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq132697 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq132697 eq16
    | (have j1 := eq132697 (τ X1) X0
       grind)
    | exact resolve eq16 eq132697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132744 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq132697 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq132697 X0 (σ X0)
       grind)
    | exact superpose eq132697 eq9
    | (have j1 := eq132697 X1 X0
       grind)
    | exact resolve eq9 eq132697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132697
  have eq132780 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq132743 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq132743
    | (have j0 := eq132743 X0 X1
       grind)
    | exact resolve eq132743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132743
  have eq132786 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132780 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq132780
    | (have j0 := eq132780 X0 X1
       grind)
    | exact resolve eq132780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132780
  have eq133092 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq132786 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq132786 (k (τ X0) X1) X1
       grind)
    | exact superpose eq132786 eq16
    | (have j1 := eq132786 X0 (τ X1)
       grind)
    | exact resolve eq16 eq132786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133103 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133092 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq133092
    | (have j0 := eq133092 X0 X1
       grind)
    | exact resolve eq133092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133092
  have eq133300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq132744 (σ X0) X1
       grind)
    | exact superpose eq132744 eq13
    | (have j1 := eq132744 (σ X0) X1
       grind)
    | exact resolve eq13 eq132744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132744
  have eq133316 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133300 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133300
    | (have j0 := eq133300 X0 X1
       grind)
    | exact resolve eq133300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133300
  have eq133916 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (σ (τ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 X0
       have i₂ := eq133103 (τ X0) X1
       grind)
    | exact superpose eq133103 eq76
    | (have j1 := eq133103 (τ X0) X1
       grind)
    | exact resolve eq76 eq133103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133103
  have eq133919 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133916 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133916
    | (have j0 := eq133916 X0 X1
       grind)
    | exact resolve eq133916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133916
  have eq134384 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq133316 x y
       grind)
    | exact superpose eq133316 eq14
    | (have j1 := eq133316 x y
       grind)
    | exact resolve eq14 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134513 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134384
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq134384
    | exact resolve eq134384 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512 eq134384
  have eq134568 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq134513
       have i₂ := eq8038
       grind)
    | exact superpose eq8038 eq134513
    | (have r₁ := eq134513
       have r₂ := eq8038
       grind)
    | exact resolve eq134513 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038
  have eq134571 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq134568
  have eq134693 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq134571
       grind)
    | exact superpose eq134571 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq134571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134727 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq132786 y y
       have i₂ := eq134571
       grind)
    | exact superpose eq134571 eq132786
    | exact resolve eq132786 eq134571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134571
  have eq134732 : x = (M.op y y) ∨ x = y := by grind
  clear eq134727
  have eq134748 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq134693
  have eq135319 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq134748
  have eq135339 : x = (M.op y y) := by
    first
    | (have r₁ := eq135319
       have r₂ := eq134732
       grind)
    | exact resolve eq135319 eq134732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134732 eq135319
  have eq135395 : y = (k (M.op y x) y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1530 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq1530
    | exact resolve eq1530 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq135413 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq85493 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq85493
    | (have j0 := eq85493 y
       grind)
    | exact resolve eq85493 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85493
  have eq135420 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq8
    | exact resolve eq8 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135422 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq18
    | exact resolve eq18 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq135425 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30 X0 y y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq30
    | exact resolve eq30 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq135464 : ∀ X0 X1 X2 : G, (M.op x X0) ≠ X0 ∨ (k (M.op X1 X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 y y X0 X1 X2
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq237
    | (have j0 := eq237 X0 X1 X0 X1 X2
       grind)
    | exact resolve eq237 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq135626 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op x (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq135420 (σ X0)
       have i₂ := eq133316 X0 X0
       grind)
    | exact superpose eq133316 eq135420
    | (have j1 := eq133316 X0 X0
       grind)
    | exact resolve eq135420 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135659 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq135420 y
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq135420
    | exact resolve eq135420 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136112 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq93 y x
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq93
    | (have j0 := eq93 y x
       grind)
    | exact resolve eq93 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136200 : (τ x) ≠ (τ (M.op x y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq119893 y x
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq119893
    | (have j0 := eq119893 y x
       grind)
    | exact resolve eq119893 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119893
  have eq136399 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op x X2) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (σ X0) (σ X1) X2
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq135422
    | (have j1 := eq394 X0 X1
       grind)
    | exact resolve eq135422 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136406 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) X2) = (M.op x X2) ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (σ X0) (σ X1) X2
       have i₂ := eq133316 X0 X1
       grind)
    | exact superpose eq133316 eq135422
    | (have j1 := eq133316 X0 X1
       grind)
    | exact resolve eq135422 eq133316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133316
  have eq136454 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op x X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135422 (τ X0) (τ X0) X1
       have i₂ := eq6411 X0
       grind)
    | exact superpose eq6411 eq135422
    | (have j1 := eq6411 X0
       grind)
    | exact resolve eq135422 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139930 : (σ y) = (σ (M.op (M.op y x) y)) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq32894 (M.op y x) y
       have i₂ := eq135395
       grind)
    | exact superpose eq135395 eq32894
    | (have j0 := eq32894 (M.op y x) y
       grind)
    | exact resolve eq32894 eq135395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32894 eq135395
  have eq139941 : (σ y) = (σ (M.op y (M.op y y))) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139930
       have i₂ := eq8 y y x
       grind)
    | exact superpose eq8 eq139930
    | exact resolve eq139930 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139930
  have eq139969 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139941
       have i₂ := eq135420 y
       grind)
    | exact superpose eq135420 eq139941
    | exact resolve eq139941 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139941
  have eq139996 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq139969
       have r₂ := eq134513
       grind)
    | exact resolve eq139969 eq134513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139969
  have eq140017 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq139996
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq139996
    | exact resolve eq139996 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139996
  have eq140027 : (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq140017
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq140017
    | exact resolve eq140017 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140017
  have eq142217 : ∀ X0 X1 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k (M.op X0 X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq135464 (M.op x x) X0 X1
       have i₂ := eq135420 x
       grind)
    | exact superpose eq135420 eq135464
    | (have j0 := eq135464 (M.op x x) X0 X1
       grind)
    | (have r₁ := eq135464 (M.op x x) X1 x
       have r₂ := eq135420 x
       grind)
    | exact resolve eq135464 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135464
  have eq142218 : ∀ X0 X1 : G, (M.op x x) = (k (M.op X0 X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have j0 := eq142217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142217
  have eq142593 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq390 (M.op x x)
       have i₂ := eq142218 x x
       grind)
    | exact superpose eq142218 eq390
    | (have j0 := eq390 (M.op x x)
       grind)
    | exact resolve eq390 eq142218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq142595 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by
    first
    | (have i₁ := eq812 (M.op x x)
       have i₂ := eq142218 x x
       grind)
    | exact superpose eq142218 eq812
    | (have j0 := eq812 (M.op x x)
       grind)
    | exact resolve eq812 eq142218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq142218
  have eq142651 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x x))) := by grind
  clear eq142595
  have eq142653 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
  clear eq142593
  have eq144481 : (σ x) ≠ (σ y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq134513
       have i₂ := eq140027
       grind)
    | exact superpose eq140027 eq134513
    | exact resolve eq134513 eq140027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134513 eq140027
  have eq144531 : (σ x) ≠ (σ y) ∨ x = (k y y) := by grind
  clear eq144481
  have eq144552 : x = (k y y) := by
    first
    | (have r₁ := eq144531
       have r₂ := eq128823
       grind)
    | exact resolve eq144531 eq128823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128823 eq144531
  have eq144684 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq132786 X0 y
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq132786
    | (have j0 := eq132786 X0 y
       grind)
    | exact resolve eq132786 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132786
  have eq144915 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op (σ X0) y)) ∨ (σ X0) = x := by
    intro X0
    first
    | (have i₁ := eq40 X0 y
       have i₂ := eq144684 (σ X0)
       grind)
    | exact superpose eq144684 eq40
    | (have j1 := eq144684 (σ X0)
       grind)
    | exact resolve eq40 eq144684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144924 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq144684 (τ X0)
       grind)
    | exact superpose eq144684 eq16
    | (have j1 := eq144684 (τ X0)
       grind)
    | exact resolve eq16 eq144684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144684
  have eq145731 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (k X1 (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5350 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5350
    | exact resolve eq5350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq145738 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145731 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq145731
    | (have j0 := eq145731 X0 X1
       grind)
    | exact resolve eq145731 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145731
  have eq145743 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op x X0) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145738 X0 X1
       have i₂ := eq135420 X0
       grind)
    | exact superpose eq135420 eq145738
    | (have j0 := eq145738 X0 X1
       grind)
    | exact resolve eq145738 eq135420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135420 eq145738
  have eq145747 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op x X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq145743 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq145743
    | (have j0 := eq145743 X0 X1
       grind)
    | exact resolve eq145743 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145743
  have eq156830 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) x) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq142651
       have i₂ := eq2393 x x
       grind)
    | (have i₁ := eq142651
       have i₂ := eq2393 X0 (τ (M.op x x))
       grind)
    | exact superpose eq2393 eq142651
    | (have j1 := eq2393 x X0
       grind)
    | exact resolve eq142651 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq156989 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq135422 (τ (M.op x x)) (τ (M.op x x)) X0
       have i₂ := eq142651
       grind)
    | exact superpose eq142651 eq135422
    | exact resolve eq135422 eq142651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157148 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op x X1) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq156989 X1
       have i₂ := eq5020 X0 x
       grind)
    | (have i₁ := eq156989 X0
       have i₂ := eq5020 (M.op x x) X1
       grind)
    | exact superpose eq5020 eq156989
    | (have j1 := eq5020 X0 x
       grind)
    | exact resolve eq156989 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157184 : (τ (M.op x x)) = (M.op x (τ (M.op x x))) := by
    first
    | (have i₁ := eq142651
       have i₂ := eq156989 (τ (M.op x x))
       grind)
    | exact superpose eq156989 eq142651
    | exact resolve eq142651 eq156989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142651 eq156989
  have eq157452 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq157184
       have i₂ := eq5020 (M.op x x) x
       grind)
    | (have i₁ := eq157184
       have i₂ := eq5020 X0 x
       grind)
    | exact superpose eq5020 eq157184
    | (have j1 := eq5020 X0 x
       grind)
    | exact resolve eq157184 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020 eq157184
  have eq158807 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq135422 (σ (M.op x x)) (σ (M.op x x)) X0
       have i₂ := eq142653
       grind)
    | exact superpose eq142653 eq135422
    | exact resolve eq135422 eq142653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159047 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
    first
    | (have i₁ := eq142653
       have i₂ := eq158807 (σ (M.op x x))
       grind)
    | exact superpose eq158807 eq142653
    | exact resolve eq142653 eq158807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142653 eq158807
  have eq159338 : ∀ X0 : G, (σ X0) = (M.op x (σ X0)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq159047
       have i₂ := eq37616 (M.op x x) x
       grind)
    | (have i₁ := eq159047
       have i₂ := eq37616 X0 x
       grind)
    | exact superpose eq37616 eq159047
    | (have j1 := eq37616 X0 x
       grind)
    | exact resolve eq159047 eq37616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37616 eq159047
  have eq161342 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq920 X0 X0
       have i₂ := eq156830 (τ X0)
       grind)
    | exact superpose eq156830 eq920
    | (have j0 := eq920 X0 X0
       have j1 := eq156830 (τ X0)
       grind)
    | exact resolve eq920 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq161343 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq156830 (τ (τ X0))
       grind)
    | exact superpose eq156830 eq176
    | (have j1 := eq156830 (τ (τ X0))
       grind)
    | exact resolve eq176 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161346 : ∀ X0 : G, (k X0 (τ x)) = (τ (M.op (σ X0) x)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0 x
       have i₂ := eq156830 X0
       grind)
    | exact superpose eq156830 eq40
    | (have j1 := eq156830 X0
       grind)
    | exact resolve eq40 eq156830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156830
  have eq161369 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq161343 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq161343
    | (have j0 := eq161343 X0
       grind)
    | exact resolve eq161343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161343
  have eq161370 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq161342 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161342
    | (have j0 := eq161342 X0
       grind)
    | exact resolve eq161342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161342
  have eq161371 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ (τ X0)) x) = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have j0 := eq161370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161370
  have eq161399 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ (τ (τ X0))) x) = (k (σ (τ (τ X0))) x) := by
    intro X0
    first
    | (have i₁ := eq161369 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161369
    | (have j0 := eq161369 X0
       grind)
    | exact resolve eq161369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161369
  have eq161400 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161371 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq161371
    | (have j0 := eq161371 X0
       grind)
    | exact resolve eq161371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161371
  have eq161408 : ∀ X0 : G, (M.op (τ X0) x) = (k (τ X0) x) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq161399 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq161399
    | (have j0 := eq161399 X0
       grind)
    | exact resolve eq161399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161399
  have eq161554 : ∀ X0 : G, X0 ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq32850 X0
       have i₂ := eq161400 X0
       grind)
    | exact superpose eq161400 eq32850
    | (have j0 := eq32850 X0
       have j1 := eq161400 X0
       grind)
    | (have r₁ := eq32850 X0
       have r₂ := eq161400 X0
       grind)
    | exact resolve eq32850 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32850
  have eq161605 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq161400 X0
       grind)
    | exact superpose eq161400 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq161400 X0
       grind)
    | exact resolve eq12 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161663 : x = y ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq144552
       have i₂ := eq161400 y
       grind)
    | exact superpose eq161400 eq144552
    | (have j1 := eq161400 y
       grind)
    | exact resolve eq144552 eq161400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161400
  have eq161673 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161605
  have eq161677 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161554 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161554
  have eq161691 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq161663
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq161663
    | exact resolve eq161663 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161663
  have eq162057 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq161673 (τ (τ X0))
       grind)
    | exact superpose eq161673 eq176
    | (have j1 := eq161673 (τ (τ X0))
       grind)
    | exact resolve eq176 eq161673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq161673
  have eq162161 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq162057 X0
       have i₂ := eq10 (τ X0)
       grind)
    | exact superpose eq10 eq162057
    | (have j0 := eq162057 X0
       grind)
    | exact resolve eq162057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162057
  have eq162179 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq162161 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq162161
    | (have j0 := eq162161 X0
       grind)
    | exact resolve eq162161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162161
  have eq162591 : ∀ X0 : G, (τ (M.op X0 y)) = (k (τ X0) (τ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq144915 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144915
    | exact resolve eq144915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144915
  have eq162618 : ∀ X0 : G, (τ (k X0 y)) = (τ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq162591 X0
       have i₂ := eq76 y X0
       grind)
    | exact superpose eq76 eq162591
    | (have j0 := eq162591 X0
       grind)
    | exact resolve eq162591 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162591
  have eq162774 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq144924 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144924
    | exact resolve eq144924 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162804 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq162774 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq162774
    | (have j0 := eq162774 X0
       grind)
    | exact resolve eq162774 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162774
  have eq163255 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq161408 X0
       grind)
    | exact superpose eq161408 eq16
    | (have j1 := eq161408 X0
       grind)
    | exact resolve eq16 eq161408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161408
  have eq163400 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1005 x X0
       have i₂ := eq157452 X0
       grind)
    | exact superpose eq157452 eq1005
    | (have j0 := eq1005 x X0
       have j1 := eq157452 X0
       grind)
    | exact resolve eq1005 eq157452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq157452
  have eq163485 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq163400 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163400
    | (have j0 := eq163400 X0
       grind)
    | exact resolve eq163400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163400
  have eq163486 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq163485 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163485
  have eq163563 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ x)) X0) ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (σ x)
       have i₂ := eq163486 (τ X0)
       grind)
    | exact superpose eq163486 eq17
    | (have j1 := eq163486 (τ X0)
       grind)
    | exact resolve eq17 eq163486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163586 : ∀ X0 : G, (k (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq163563 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163563
    | (have j0 := eq163563 X0
       grind)
    | exact resolve eq163563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163563
  have eq163669 : ∀ X0 : G, (M.op (τ X0) x) = (k (τ X0) x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq159338 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159338
    | (have j0 := eq159338 (τ X0)
       grind)
    | exact resolve eq159338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159338
  have eq165548 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (τ (k X0 X1)) X2) ∨ (k X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135422 (τ X0) (τ X1) X2
       have i₂ := eq133919 X0 X1
       grind)
    | exact superpose eq133919 eq135422
    | (have j1 := eq133919 X0 X1
       grind)
    | exact resolve eq135422 eq133919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133919
  have eq168062 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq136399 y y x
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq136399
    | exact resolve eq136399 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136399
  have eq168251 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq168062 (σ y)
       grind)
    | exact superpose eq168062 eq14
    | exact resolve eq14 eq168062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168062
  have eq169063 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ (σ X1))) ∨ (M.op (σ (k X0 (σ X1))) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (σ X1)
       have i₂ := eq136406 X0 (σ X1) X2
       grind)
    | (have i₁ := eq40 X0 X1
       have i₂ := eq136406 (k (σ X0) X1) X1 X2
       grind)
    | exact superpose eq136406 eq40
    | (have j1 := eq136406 X0 (σ X1) X2
       grind)
    | exact resolve eq40 eq136406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136406
  have eq169077 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 X1) ∨ (M.op (σ (k X0 (σ X1))) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169063 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq169063
    | (have j0 := eq169063 X0 X1 X2
       grind)
    | exact resolve eq169063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169063
  have eq171862 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6411 X0
       have i₂ := eq136454 X0 (τ X0)
       grind)
    | exact superpose eq136454 eq6411
    | (have j0 := eq6411 X0
       have j1 := eq136454 X0 x
       grind)
    | exact resolve eq6411 eq136454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411 eq136454
  have eq172023 : ∀ X0 : G, (τ X0) = (M.op x (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq171862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171862
  have eq172683 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (σ X0)) = (M.op x (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq172023 (σ X0)
       grind)
    | exact superpose eq172023 eq13
    | (have j1 := eq172023 (σ X0)
       grind)
    | exact resolve eq13 eq172023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172023
  have eq172699 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq172683 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq172683
    | (have j0 := eq172683 X0
       grind)
    | exact resolve eq172683 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172683
  have eq174884 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ (k y y) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165548 X0 y X1
       have i₂ := eq162618 X0
       grind)
    | exact superpose eq162618 eq165548
    | (have j0 := eq165548 X0 y x
       have j1 := eq162618 X0
       grind)
    | exact resolve eq165548 eq162618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162618 eq165548
  have eq175140 : ∀ X0 X1 : G, x = X0 ∨ (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq174884 X0 X1
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq174884
    | (have j0 := eq174884 X0 X1
       grind)
    | exact resolve eq174884 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174884
  have eq175141 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op X0 y)) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq175140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175140
  have eq175218 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (τ (M.op x y)) X0) ∨ (M.op X1 X2) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175141 (M.op X1 X2) X0
       have i₂ := eq135422 X1 X2 y
       grind)
    | exact superpose eq135422 eq175141
    | (have j0 := eq175141 x X0
       grind)
    | exact resolve eq175141 eq135422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175141
  have eq178455 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op x X1) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135422 (σ X0) (σ X0) X1
       have i₂ := eq172699 X0
       grind)
    | exact superpose eq172699 eq135422
    | (have j1 := eq172699 X0
       grind)
    | exact resolve eq135422 eq172699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172699
  have eq179543 : ∀ X0 : G, (σ (τ X0)) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (τ X0) (τ x)) = (τ (M.op (σ (τ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq78209 X0
       have i₂ := eq161346 (τ X0)
       grind)
    | exact superpose eq161346 eq78209
    | (have j0 := eq78209 X0
       have j1 := eq161346 (τ X0)
       grind)
    | exact resolve eq78209 eq161346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78209 eq161346
  have eq179552 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ X0) (τ x)) = (τ (M.op (σ (τ X0)) x)) := by
    intro X0
    first
    | (have j0 := eq179543 X0
       grind)
    | (have r₁ := eq179543 X0
       have r₂ := eq10 X0
       grind)
    | exact resolve eq179543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179543
  have eq179569 : ∀ X0 : G, (τ (M.op X0 x)) = (k (τ X0) (τ x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179552 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq179552
    | (have j0 := eq179552 X0
       grind)
    | exact resolve eq179552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179552
  have eq179571 : ∀ X0 : G, (τ (k X0 x)) = (τ (M.op X0 x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179569 X0
       have i₂ := eq76 x X0
       grind)
    | exact superpose eq76 eq179569
    | (have j0 := eq179569 X0
       grind)
    | exact resolve eq179569 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq179569
  have eq179726 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 x)) = (τ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq179571 X0
       grind)
    | exact superpose eq179571 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq179571 X0
       grind)
    | exact resolve eq12 eq179571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179571
  have eq179740 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 x)) = (τ (M.op X0 x)) := by
    intro X0
    first
    | (have j0 := eq179726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179726
  have eq181692 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq178455 y X0
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq178455
    | (have j0 := eq178455 y x
       grind)
    | exact resolve eq178455 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178455
  have eq181838 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181692 (σ y)
       grind)
    | exact superpose eq181692 eq14
    | exact resolve eq14 eq181692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181692
  have eq182163 : ∀ X0 : G, (σ (M.op x (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq161677 X0
       have i₂ := eq157148 X0 (τ X0)
       grind)
    | exact superpose eq157148 eq161677
    | (have j0 := eq161677 X0
       have j1 := eq157148 X0 x
       grind)
    | exact resolve eq161677 eq157148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157148 eq161677
  have eq182237 : ∀ X0 : G, (σ (M.op x (τ X0))) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq182163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182163
  have eq182264 : ∀ X0 : G, (M.op (σ X0) x) = (k (σ X0) x) ∨ (σ X0) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq182237 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182237
    | (have j0 := eq182237 (σ X0)
       grind)
    | exact resolve eq182237 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182237
  have eq182538 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ x)) = (σ (M.op (τ (σ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq163255 (σ X0)
       grind)
    | exact superpose eq163255 eq40
    | (have j1 := eq163255 (σ X0)
       grind)
    | exact resolve eq40 eq163255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq163255
  have eq182549 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ x)) = (σ (M.op (τ (σ X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq182538 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182538
    | (have j0 := eq182538 X0
       grind)
    | exact resolve eq182538 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182538
  have eq182564 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ X0) (σ x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182549 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq182549
    | (have j0 := eq182549 X0
       grind)
    | exact resolve eq182549 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182549
  have eq182569 : ∀ X0 : G, (σ (M.op X0 x)) = (σ (k X0 x)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182564 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq182564
    | (have j0 := eq182564 X0
       grind)
    | exact resolve eq182564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182564
  have eq182722 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq182569 X0
       grind)
    | exact superpose eq182569 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq182569 X0
       grind)
    | exact resolve eq12 eq182569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182569
  have eq182736 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have j0 := eq182722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182722
  have eq186277 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op (τ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq175218 X0 (τ (M.op x y)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175218
  have eq214113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq162179 X0
       grind)
    | exact superpose eq162179 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq162179 X0
       grind)
    | exact resolve eq12 eq162179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162179
  have eq214117 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ (τ X0)) x) = (M.op (τ (τ X0)) x) := by
    intro X0
    first
    | (have j0 := eq214113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214113
  have eq223699 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op x X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq145747 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145747
    | exact resolve eq145747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223711 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq145747 X0 x
       have i₂ := eq163486 X0
       grind)
    | exact superpose eq163486 eq145747
    | (have j1 := eq163486 X0
       grind)
    | exact resolve eq145747 eq163486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145747 eq163486
  have eq223736 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq223711 X0
       have j1 := eq135425 X0
       grind)
    | (have r₁ := eq223711 X0
       have r₂ := eq135425 X0
       grind)
    | exact resolve eq223711 eq135425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135425 eq223711
  have eq224839 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) x) = (k (σ y) x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq223736 (σ y)
       grind)
    | exact superpose eq223736 eq14
    | (have j1 := eq223736 (σ y)
       grind)
    | exact resolve eq14 eq223736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223736
  have eq224995 : (M.op (σ y) x) = (k (σ y) x) := by
    first
    | (have j1 := eq182264 y
       grind)
    | (have r₁ := eq224839
       have r₂ := eq182264 y
       grind)
    | exact resolve eq224839 eq182264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182264 eq224839
  have eq225376 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq223699 (σ (σ x)) X0
       have i₂ := eq163586 X0
       grind)
    | exact superpose eq163586 eq223699
    | (have j0 := eq223699 (τ X0) x
       have j1 := eq163586 X0
       grind)
    | exact resolve eq223699 eq163586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163586 eq223699
  have eq225570 : ∀ X0 : G, (M.op (σ (σ x)) X0) = X0 ∨ (M.op (τ X0) x) = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq225376 X0
       have j1 := eq163669 X0
       grind)
    | (have r₁ := eq225376 X0
       have r₂ := eq163669 X0
       grind)
    | exact resolve eq225376 eq163669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163669 eq225376
  have eq246612 : (M.op (σ y) (σ x)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq135626 y
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq135626
    | exact resolve eq135626 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135626
  have eq246666 : (σ (k y x)) = (M.op x (σ y)) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq394 y x
       have i₂ := eq246612
       grind)
    | exact superpose eq246612 eq394
    | (have j0 := eq394 y x
       grind)
    | exact resolve eq394 eq246612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq250197 : ∀ X0 X1 X2 : G, (k X0 X0) = X1 ∨ (M.op x X2) = (M.op (σ (k (σ X1) (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1
       have i₂ := eq169077 (σ X1) X0 X2
       grind)
    | exact superpose eq169077 eq9
    | (have j1 := eq169077 (σ X1) X0 X2
       grind)
    | exact resolve eq9 eq169077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169077
  have eq250233 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op (σ (σ (k X1 X0))) X2) ∨ (k X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250197 X0 X1 X2
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq250197
    | (have j0 := eq250197 X0 X1 X2
       grind)
    | exact resolve eq250197 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250197
  have eq250258 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ (k y y) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250233 y X0 X1
       have i₂ := eq162804 X0
       grind)
    | exact superpose eq162804 eq250233
    | (have j0 := eq250233 y X0 x
       have j1 := eq162804 X0
       grind)
    | exact resolve eq250233 eq162804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162804 eq250233
  have eq250330 : ∀ X0 X1 : G, x = X0 ∨ (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq250258 X0 X1
       have i₂ := eq144552
       grind)
    | exact superpose eq144552 eq250258
    | (have j0 := eq250258 X0 X1
       grind)
    | exact resolve eq250258 eq144552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144552 eq250258
  have eq250331 : ∀ X0 X1 : G, (M.op x X1) = (M.op (σ (σ (M.op X0 y))) X1) ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq250330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250330
  have eq250350 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (σ (σ (M.op x y))) X0) ∨ (M.op X1 X2) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq250331 (M.op X1 X2) X0
       have i₂ := eq135422 X1 X2 y
       grind)
    | exact superpose eq135422 eq250331
    | (have j0 := eq250331 x X0
       grind)
    | exact resolve eq250331 eq135422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135422 eq250331
  have eq251216 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op (σ (σ (M.op x y))) X0) := by
    intro X0
    first
    | (have j0 := eq250350 X0 (σ (σ (M.op x y))) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250350
  have eq261067 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq246666
       have i₂ := eq161691
       grind)
    | exact superpose eq161691 eq246666
    | exact resolve eq246666 eq161691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246666
  have eq261069 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq261067
  have eq261070 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq261069
       have r₂ := eq168251
       grind)
    | exact resolve eq261069 eq168251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261069
  have eq261106 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq136112
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq136112
    | (have r₁ := eq136112
       have r₂ := eq261070
       grind)
    | exact resolve eq136112 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136112
  have eq261108 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq136200
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq136200
    | exact resolve eq136200 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136200
  have eq261135 : (σ x) ≠ (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq181838
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq181838
    | exact resolve eq181838 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181838
  have eq261233 : x ≠ x ∨ x = (M.op (τ x) y) ∨ x = y := by
    first
    | (have i₁ := eq186277 y
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq186277
    | (have r₁ := eq186277 y
       have r₂ := eq261070
       grind)
    | exact resolve eq186277 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186277
  have eq261253 : x ≠ x ∨ x = (M.op (σ (σ x)) y) ∨ x = y := by
    first
    | (have i₁ := eq251216 y
       have i₂ := eq261070
       grind)
    | exact superpose eq261070 eq251216
    | (have r₁ := eq251216 y
       have r₂ := eq261070
       grind)
    | exact resolve eq251216 eq261070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251216 eq261070
  have eq261440 : x = (M.op (σ (σ x)) y) ∨ x = y := by grind
  clear eq261253
  have eq261443 : x = (M.op (τ x) y) ∨ x = y := by grind
  clear eq261233
  have eq261456 : (σ x) ≠ (M.op x (σ y)) ∨ x = y := by grind
  clear eq261135
  have eq261461 : (τ x) = (τ (k y x)) ∨ x = y := by grind
  clear eq261108
  have eq261463 : x = (k y x) ∨ x = y := by grind
  clear eq261106
  have eq261621 : (τ x) = (τ (M.op y x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq179740 y
       have i₂ := eq261463
       grind)
    | exact superpose eq261463 eq179740
    | (have j0 := eq179740 y
       grind)
    | exact resolve eq179740 eq261463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179740
  have eq261626 : (σ x) = (σ (M.op y x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq182736 y
       have i₂ := eq261463
       grind)
    | exact superpose eq261463 eq182736
    | (have j0 := eq182736 y
       grind)
    | exact resolve eq182736 eq261463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182736 eq261463
  have eq261768 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq261626
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq261626
    | exact resolve eq261626 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261626
  have eq261773 : (τ x) = (τ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq261621
       have i₂ := eq135659
       grind)
    | exact superpose eq135659 eq261621
    | exact resolve eq261621 eq135659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135659 eq261621
  have eq261828 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq261768
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq261768
    | exact resolve eq261768 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261768
  have eq261829 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq261828
  have eq261834 : x = y ∨ (τ x) = (τ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq261773
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq261773
    | exact resolve eq261773 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261773
  have eq261835 : (τ x) = (τ (M.op x y)) ∨ x = y := by grind
  clear eq261834
  have eq261863 : (σ x) = (k x (σ y)) ∨ x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq144924 x
       have i₂ := eq261443
       grind)
    | exact superpose eq261443 eq144924
    | (have j0 := eq144924 x
       grind)
    | exact resolve eq144924 eq261443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144924 eq261443
  have eq263010 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op x y)
       have i₂ := eq261829
       grind)
    | exact superpose eq261829 eq13
    | exact resolve eq13 eq261829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261829
  have eq263071 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (k X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq263010 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq263010
    | exact resolve eq263010 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263010
  have eq263463 : x = y ∨ (k (τ y) x) = (M.op (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq225570 y
       have i₂ := eq261440
       grind)
    | exact superpose eq261440 eq225570
    | (have j0 := eq225570 y
       grind)
    | exact resolve eq225570 eq261440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225570 eq261440
  have eq263665 : (k (τ y) x) = (M.op (τ y) x) ∨ x = y := by grind
  clear eq263463
  have eq266141 : (σ x) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq28 x (σ y)
       have i₂ := eq261863
       grind)
    | exact superpose eq261863 eq28
    | exact resolve eq28 eq261863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq261863
  have eq266143 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq266141
       have r₂ := eq261456
       grind)
    | exact resolve eq266141 eq261456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261456 eq266141
  have eq266157 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq266143
       grind)
    | exact superpose eq266143 eq10
    | exact resolve eq10 eq266143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266143
  have eq266179 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq266157
       grind)
    | exact superpose eq266157 eq9
    | exact resolve eq9 eq266157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266157
  have eq266191 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq266179
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq266179
    | exact resolve eq266179 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266179
  have eq266192 : x = (σ x) ∨ x = y := by grind
  clear eq266191
  have eq266278 : (M.op x (σ y)) = (M.op (σ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq246612
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq246612
    | exact resolve eq246612 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246612
  have eq266293 : x = (τ x) ∨ x = y := by
    first
    | (have i₁ := eq9 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq9
    | exact resolve eq9 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266295 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq13
    | exact resolve eq13 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266300 : ∀ X0 : G, (τ (k X0 x)) = (k (τ X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq266192
       grind)
    | exact superpose eq266192 eq24
    | exact resolve eq24 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq266522 : (M.op x (σ y)) = (M.op (σ y) x) ∨ x = y := by grind
  clear eq266278
  have eq267942 : ∀ X0 : G, (k X0 x) = (σ (k (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq266295 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266295
    | exact resolve eq266295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266295
  have eq268115 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq267942 X0
       have i₂ := eq16 X0 x
       grind)
    | exact superpose eq16 eq267942
    | exact resolve eq267942 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267942
  have eq268924 : (τ x) = (k (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq261461
       have i₂ := eq266300 y
       grind)
    | exact superpose eq266300 eq261461
    | exact resolve eq261461 eq266300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261461
  have eq268937 : (τ x) = (k (τ y) x) ∨ x = y := by grind
  clear eq268924
  have eq269053 : (τ x) = (M.op (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq263665
       have i₂ := eq268937
       grind)
    | exact superpose eq268937 eq263665
    | exact resolve eq263665 eq268937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263665
  have eq269148 : (τ x) = (M.op (τ y) x) ∨ x = y := by grind
  clear eq269053
  have eq269385 : x ≠ (τ x) ∨ x = (k (τ y) x) ∨ x = y := by
    first
    | (have i₁ := eq93 (τ y) x
       have i₂ := eq269148
       grind)
    | exact superpose eq269148 eq93
    | (have j0 := eq93 (τ y) x
       grind)
    | exact resolve eq93 eq269148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269148
  have eq269558 : x = (k (τ y) x) ∨ x = y := by
    first
    | (have r₁ := eq269385
       have r₂ := eq266293
       grind)
    | exact resolve eq269385 eq266293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266293 eq269385
  have eq269649 : (τ x) = (k (τ (τ y)) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq266300 (τ y)
       have i₂ := eq269558
       grind)
    | exact superpose eq269558 eq266300
    | exact resolve eq266300 eq269558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266300 eq269558
  have eq269694 : (τ x) = (k (τ (τ y)) x) ∨ x = y := by grind
  clear eq269649
  have eq271178 : (τ x) = (M.op (τ (τ y)) x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq214117 y
       have i₂ := eq269694
       grind)
    | exact superpose eq269694 eq214117
    | (have j0 := eq214117 y
       grind)
    | exact resolve eq214117 eq269694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214117
  have eq271186 : (σ (τ x)) = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 (τ y) x
       have i₂ := eq269694
       grind)
    | exact superpose eq269694 eq16
    | exact resolve eq16 eq269694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269694
  have eq271238 : x = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq271186
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq271186
    | exact resolve eq271186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271186
  have eq271241 : x = y ∨ (τ x) = (M.op (τ (τ y)) x) ∨ x = y := by
    first
    | (have i₁ := eq271178
       have i₂ := eq135339
       grind)
    | exact superpose eq135339 eq271178
    | exact resolve eq271178 eq135339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271178
  have eq271242 : (τ x) = (M.op (τ (τ y)) x) ∨ x = y := by grind
  clear eq271241
  have eq271267 : (σ x) = (k y (σ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq16 y (σ x)
       have i₂ := eq271238
       grind)
    | exact superpose eq271238 eq16
    | exact resolve eq16 eq271238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271238
  have eq271755 : (σ x) ≠ (σ (τ x)) ∨ (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have i₁ := eq85463 (τ (τ y)) x
       have i₂ := eq271242
       grind)
    | exact superpose eq271242 eq85463
    | (have j0 := eq85463 (τ (τ y)) x
       grind)
    | exact resolve eq85463 eq271242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85463 eq271242
  have eq271903 : x ≠ (σ x) ∨ (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have i₁ := eq271755
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq271755
    | exact resolve eq271755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271755
  have eq271930 : (σ x) = (σ (k (τ (τ y)) x)) ∨ x = y := by
    first
    | (have r₁ := eq271903
       have r₂ := eq266192
       grind)
    | exact resolve eq271903 eq266192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266192 eq271903
  have eq271933 : (σ x) = (k (τ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq271930
       have i₂ := eq16 (τ y) x
       grind)
    | exact superpose eq16 eq271930
    | exact resolve eq271930 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271930
  have eq272573 : (σ x) = (k (τ y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268115 (τ y)
       have i₂ := eq271933
       grind)
    | exact superpose eq271933 eq268115
    | exact resolve eq268115 eq271933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271933
  have eq272596 : (σ x) = (k (τ y) x) ∨ x = y := by grind
  clear eq272573
  have eq272642 : (σ x) = (τ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268937
       have i₂ := eq272596
       grind)
    | exact superpose eq272596 eq268937
    | exact resolve eq268937 eq272596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268937
  have eq272656 : (σ (σ x)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq272596
       grind)
    | exact superpose eq272596 eq16
    | exact resolve eq16 eq272596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq272596
  have eq272739 : (σ x) = (τ x) ∨ x = y := by grind
  clear eq272642
  have eq272884 : x = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq272739
       grind)
    | exact superpose eq272739 eq10
    | exact resolve eq10 eq272739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272739
  have eq273665 : (k y x) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq268115 y
       have i₂ := eq272656
       grind)
    | exact superpose eq272656 eq268115
    | exact resolve eq268115 eq272656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268115 eq272656
  have eq273701 : (k y x) = (σ (σ x)) ∨ x = y := by grind
  clear eq273665
  have eq273757 : (M.op x y) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq161691
       have i₂ := eq273701
       grind)
    | exact superpose eq273701 eq161691
    | exact resolve eq161691 eq273701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161691
  have eq273902 : (M.op x y) = (σ (σ x)) ∨ x = y := by grind
  clear eq273757
  have eq274089 : (σ x) = (k y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq271267
       have i₂ := eq273902
       grind)
    | exact superpose eq273902 eq271267
    | exact resolve eq271267 eq273902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271267
  have eq274122 : (σ x) = (k y (M.op x y)) ∨ x = y := by grind
  clear eq274089
  have eq274300 : (σ (k y x)) = (σ (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq263071 y
       have i₂ := eq274122
       grind)
    | exact superpose eq274122 eq263071
    | exact resolve eq263071 eq274122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263071
  have eq274334 : (σ (k y x)) = (σ (σ x)) ∨ x = y := by grind
  clear eq274300
  have eq274645 : (σ (σ x)) = (σ (σ (σ x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274334
       have i₂ := eq273701
       grind)
    | exact superpose eq273701 eq274334
    | exact resolve eq274334 eq273701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273701 eq274334
  have eq274759 : (σ (σ x)) = (σ (σ (σ x))) ∨ x = y := by grind
  clear eq274645
  have eq274819 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274759
       have i₂ := eq273902
       grind)
    | exact superpose eq273902 eq274759
    | exact resolve eq274759 eq273902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273902 eq274759
  have eq274852 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq274819
  have eq274943 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq274852
       grind)
    | exact superpose eq274852 eq9
    | exact resolve eq9 eq274852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274852
  have eq275011 : (M.op x y) = (τ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq261835
       have i₂ := eq274943
       grind)
    | exact superpose eq274943 eq261835
    | exact resolve eq261835 eq274943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261835 eq274943
  have eq275065 : (M.op x y) = (τ x) ∨ x = y := by grind
  clear eq275011
  have eq275137 : (σ (τ x)) ≠ (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq168251
       have i₂ := eq275065
       grind)
    | exact superpose eq275065 eq168251
    | exact resolve eq168251 eq275065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168251
  have eq275207 : (σ x) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq274122
       have i₂ := eq275065
       grind)
    | exact superpose eq275065 eq274122
    | exact resolve eq274122 eq275065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274122 eq275065
  have eq275459 : (σ x) = (k y (τ x)) ∨ x = y := by grind
  clear eq275207
  have eq275479 : (σ (τ x)) ≠ (M.op x (σ y)) ∨ x = y := by grind
  clear eq275137
  have eq275566 : x ≠ (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq275479
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq275479
    | exact resolve eq275479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275479
  have eq275862 : (σ (σ x)) = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq17 x y
       have i₂ := eq275459
       grind)
    | exact superpose eq275459 eq17
    | exact resolve eq17 eq275459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq275459
  have eq275951 : (σ (σ x)) = (M.op (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq275862
       have i₂ := eq224995
       grind)
    | exact superpose eq224995 eq275862
    | exact resolve eq275862 eq224995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275862
  have eq276249 : x ≠ (σ (σ x)) ∨ x = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq93 (σ y) x
       have i₂ := eq275951
       grind)
    | exact superpose eq275951 eq93
    | (have j0 := eq93 (σ y) x
       grind)
    | exact resolve eq93 eq275951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq275951
  have eq276370 : x = (k (σ y) x) ∨ x = y := by
    first
    | (have r₁ := eq276249
       have r₂ := eq272884
       grind)
    | exact resolve eq276249 eq272884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272884 eq276249
  have eq276401 : x = (M.op (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq276370
       have i₂ := eq224995
       grind)
    | exact superpose eq224995 eq276370
    | exact resolve eq276370 eq224995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224995 eq276370
  have eq278916 : x = (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq276401
       have i₂ := eq266522
       grind)
    | exact superpose eq266522 eq276401
    | exact resolve eq276401 eq266522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266522 eq276401
  have eq278985 : x = (M.op x (σ y)) ∨ x = y := by grind
  clear eq278916
  have eq278999 : x = y := by
    first
    | (have r₁ := eq278985
       have r₂ := eq275566
       grind)
    | exact resolve eq278985 eq275566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275566 eq278985
  have eq279005 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq14
    | exact resolve eq14 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279084 : x = (M.op x x) := by
    first
    | (have i₁ := eq135339
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq135339
    | exact resolve eq135339 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135339
  have eq279103 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135413
       have i₂ := eq278999
       grind)
    | exact superpose eq278999 eq135413
    | exact resolve eq135413 eq278999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135413 eq278999
  have eq279438 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq279103
  have eq279484 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq279005
       have i₂ := eq279084
       grind)
    | exact superpose eq279084 eq279005
    | exact resolve eq279005 eq279084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279005 eq279084
  have eq279494 : False := by grind
  exact eq279494

/-- `Equation4392`: `x ◇ (x ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4392 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4392 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4392.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X4) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X2
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq8 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
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
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 (M.op X1 X1) X2 X3
       have i₂ := eq21 X1 X0
       grind)
    | (have i₁ := eq18 X1 (M.op X1 X1) X2 X3
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq18
    | exact resolve eq18 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (M.op X2 X2)
       have i₂ := eq21 X2 X0
       grind)
    | (have i₁ := eq8 X1 X2 (M.op X2 X2)
       have i₂ := eq21 X0 X2
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq27 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq133 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X4 X5) X4) X6) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq19 X4 X5 x X6
       have i₂ := eq19 X0 X1 x X2
       grind)
    | (have i₁ := eq19 X0 X1 (M.op (M.op X0 X1) X0) x
       have i₂ := eq19 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X3 (M.op X3 X3) X4 X5
       have i₂ := eq19 X0 X1 X3 X2
       grind)
    | (have i₁ := eq18 (M.op (M.op X0 X1) X0) X3 X3 X4
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X3)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 X4 (M.op X4 X4)
       have i₂ := eq19 X0 X1 X4 X2
       grind)
    | (have i₁ := eq8 X0 (M.op (M.op X0 X1) X0) X3
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X1 X2) X1) ∨ (M.op (M.op X1 X2) X1) = (k (M.op (M.op X1 X2) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 (M.op (M.op X1 X2) X1) X3
       have i₂ := eq19 X1 X2 X0 X3
       grind)
    | (have i₁ := eq111 X2 (M.op X2 X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq111
    | (have j0 := eq111 (M.op (M.op X1 X2) X1) X3
       grind)
    | (have r₁ := eq111 (M.op (M.op (M.op X0 X1) X0) X3) (M.op (M.op (M.op (M.op X0 X1) X0) X3) (M.op (M.op (M.op X0 X1) X0) X3))
       have r₂ := eq19 X0 X1 (M.op (M.op (M.op X0 X1) X0) X3) X3
       grind)
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X1) = (k (M.op (M.op X1 X2) X1) X3) := by
    intro X1 X2 X3
    first
    | (have j0 := eq194 x X1 X2 X3
       grind)
    | (have r₁ := eq194 x X1 X2 X3
       have r₂ := eq8 x X1 X2
       grind)
    | exact resolve eq194 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq332 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq30 X2 X2 X0 X1
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X2 (k X2 X2)
       have j1 := eq30 X3 X2 X2 X3
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (M.op X2 X3) X2) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq30 (σ X1) (σ X0) X2 X3
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) (σ X0) X2 X3
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq370 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq133 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq133
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq133 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 (M.op X2 X2)) ∨ (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 (M.op X2 (M.op X2 X2)) X3
       have i₂ := eq87 X2 X3 X0 X1
       grind)
    | (have i₁ := eq111 (M.op X2 X3) X2
       have i₂ := eq87 X0 X1 X2 X3
       grind)
    | exact superpose eq87 eq111
    | (have j0 := eq111 (M.op X2 (M.op X2 X2)) X3
       grind)
    | (have r₁ := eq111 (M.op (M.op X0 (M.op X0 X0)) X1) (M.op X0 (M.op X0 X0))
       have r₂ := eq87 X0 X1 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq111 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq758 : ∀ X2 X3 : G, (M.op X2 (M.op X2 X2)) = (k (M.op X2 (M.op X2 X2)) X3) := by
    intro X2 X3
    first
    | (have j0 := eq757 x x X2 X3
       grind)
    | (have r₁ := eq757 x X2 x X3
       have r₂ := eq8 x x X2
       grind)
    | exact resolve eq757 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq784 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq808 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq841 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1268 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (k (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq758 X0 (τ X1)
       grind)
    | exact superpose eq758 eq17
    | exact resolve eq17 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1869 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X3 X4) X3) X5) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X6) X7) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq139 X3 X4 X5 X6 (M.op X6 X6) X7
       have i₂ := eq19 X0 X1 X6 X2
       grind)
    | (have i₁ := eq139 X0 X1 X2 (M.op (M.op X0 X1) X0) X3 X6
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq139
    | exact resolve eq139 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2393 : ∀ X0 X1 X2 X3 X4 X5 X8 X9 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X8) X9) := by
    intro X0 X1 X2 X3 X4 X5 X8 X9
    first
    | (have i₁ := eq170 x x X8 X9 X4 X5
       have i₂ := eq170 X0 X1 X2 X3 x x
       grind)
    | (have i₁ := eq170 (M.op (M.op X0 X1) X0) X2 X2 X3 X4 X5
       have i₂ := eq170 X0 X1 X2 (M.op (M.op X0 X1) X0) X4 X5
       grind)
    | exact superpose eq170 eq170
    | exact resolve eq170 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq2774 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X5 (M.op X5 X5)) X6) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X4) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq87 X5 X6 X4 (M.op X4 X4)
       have i₂ := eq171 X0 X1 X2 X4 X3
       grind)
    | (have i₁ := eq87 X0 X1 (M.op (M.op (M.op X0 X1) X0) X2) X4
       have i₂ := eq171 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq171 eq87
    | exact resolve eq87 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq2948 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq3032 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = X1 ∨ (k (σ (τ X1)) X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1
       have i₂ := eq36 (τ X1) X0
       grind)
    | exact superpose eq36 eq27
    | (have j1 := eq36 (τ X1) X0
       grind)
    | exact resolve eq27 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3034 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3052 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ (τ X1)) X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3032 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3032
    | (have j0 := eq3032 X0 X1
       grind)
    | exact resolve eq3032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq3074 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2948 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2948
    | (have j0 := eq2948 X0 X1
       grind)
    | exact resolve eq2948 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948
  have eq3099 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3052 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3052
    | (have j0 := eq3052 X0 X1
       grind)
    | exact resolve eq3052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq3865 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq77 (σ y) X0 (σ x)
       grind)
    | exact superpose eq77 eq14
    | (have j1 := eq77 (σ y) x (σ x)
       grind)
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq3900 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq3865 X0
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3865
    | (have j0 := eq3865 X0
       grind)
    | exact resolve eq3865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq4758 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op (σ X0) (σ (k X0 X0))) X3) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (σ X0) X3 X1 X2
       have i₂ := eq104 X0 X0
       grind)
    | exact superpose eq104 eq87
    | (have j1 := eq104 X0 X0
       grind)
    | exact resolve eq87 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq5501 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq91
    | (have j0 := eq91 X1 (σ X0)
       grind)
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq5570 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5501 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5501
    | (have j0 := eq5501 X0 X1
       grind)
    | exact resolve eq5501 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501
  have eq6214 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq841 X0
       have i₂ := eq5570 X0 X0
       grind)
    | exact superpose eq5570 eq841
    | (have j0 := eq841 X0
       have j1 := eq5570 X0 X0
       grind)
    | (have r₁ := eq841 x
       have r₂ := eq5570 x x
       grind)
    | exact resolve eq841 eq5570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570
  have eq6241 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6214
  have eq7736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq784
       have i₂ := eq3162 y x
       grind)
    | exact superpose eq3162 eq784
    | (have j1 := eq3162 y x
       grind)
    | (have r₁ := eq784
       have r₂ := eq3162 y x
       grind)
    | exact resolve eq784 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq7737 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq784
       have i₂ := eq3074 y x
       grind)
    | exact superpose eq3074 eq784
    | (have j1 := eq3074 (σ y) (σ x)
       grind)
    | (have r₁ := eq784
       have r₂ := eq3074 y x
       grind)
    | exact resolve eq784 eq3074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq7738 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7737
  have eq7739 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq7736
  have eq7751 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq133
    | exact resolve eq133 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7810 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7751
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7751
    | exact resolve eq7751 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7751
  have eq7916 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7810
       grind)
    | exact superpose eq7810 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7919 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3074 y x
       have i₂ := eq7810
       grind)
    | exact superpose eq7810 eq3074
    | (have j0 := eq3074 y x
       grind)
    | exact resolve eq3074 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074 eq7810
  have eq7920 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq7919
  have eq7921 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq7916
  have eq8473 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq7921
       grind)
    | exact superpose eq7921 eq8
    | exact resolve eq8 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8475 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x y
       have i₂ := eq7921
       grind)
    | exact superpose eq7921 eq18
    | exact resolve eq18 eq7921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921
  have eq10722 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq7739
       grind)
    | exact superpose eq7739 eq133
    | exact resolve eq133 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq7739
  have eq10790 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10722
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10722
    | exact resolve eq10722 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722
  have eq10791 : x = (k x y) := by grind
  clear eq10790
  have eq11365 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq808 x x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq808
    | exact resolve eq808 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq11449 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11365
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11365
    | exact resolve eq11365 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq12170 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8473 (σ x)
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq8473
    | exact resolve eq8473 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12324 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq12170
  have eq13105 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8475 X0 (M.op X0 X0)
       have i₂ := eq8473 X0
       grind)
    | exact superpose eq8473 eq8475
    | exact resolve eq8475 eq8473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8473
  have eq13317 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq13105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13105
  have eq14866 : (σ (M.op x y)) ≠ (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq12324
       grind)
    | exact superpose eq12324 eq14
    | exact resolve eq14 eq12324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12324
  have eq15332 : (σ x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14866
       have i₂ := eq7920
       grind)
    | exact superpose eq7920 eq14866
    | exact resolve eq14866 eq7920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920 eq14866
  have eq15333 : (σ x) ≠ (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq15332
  have eq31624 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq370 (σ X1) X0
       grind)
    | exact superpose eq370 eq26
    | (have j1 := eq370 (σ X1) X0
       grind)
    | exact resolve eq26 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq370
  have eq31654 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31624 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31624
    | (have j0 := eq31624 X0 X1
       grind)
    | exact resolve eq31624 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31624
  have eq31694 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31654 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq31654
    | (have j0 := eq31654 X0 X1
       grind)
    | exact resolve eq31654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31654
  have eq34793 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq332 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq34794 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34793 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34793
  have eq35071 : ∀ X0 X3 : G, (k X0 X3) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X3
    first
    | (have i₁ := eq195 x x X3
       have i₂ := eq34794 X0 x x
       grind)
    | (have i₁ := eq195 x x X3
       have i₂ := eq34794 (M.op (M.op x x) x) x x
       grind)
    | exact superpose eq34794 eq195
    | (have j1 := eq34794 X0 x x
       grind)
    | exact resolve eq195 eq34794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq35131 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op x x) X1 x x
       have i₂ := eq34794 X0 (M.op x x) (M.op (M.op x x) (M.op x x))
       grind)
    | (have i₁ := eq20 X0 X1 x x
       have i₂ := eq34794 (M.op (M.op X0 (M.op X0 X0)) (M.op x x)) X1 x
       grind)
    | exact superpose eq34794 eq20
    | (have j1 := eq34794 X0 X1 x
       grind)
    | exact resolve eq20 eq34794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34794
  have eq36096 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X3) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq362 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq59799 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq11449
       grind)
    | exact superpose eq11449 eq9
    | exact resolve eq9 eq11449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq59878 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq59799
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59799
    | exact resolve eq59799 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59799
  have eq60960 : x = y ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35071 x x
       have i₂ := eq59878
       grind)
    | exact superpose eq59878 eq35071
    | exact resolve eq35071 eq59878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35071 eq59878
  have eq60965 : y = (M.op x x) ∨ x = y := by grind
  clear eq60960
  have eq131398 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq3034 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq131399 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq131398 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131398
    | (have j0 := eq131398 X0
       grind)
    | exact resolve eq131398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131398
  have eq173488 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31694 x x
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq31694
    | (have j0 := eq31694 x x
       grind)
    | exact resolve eq31694 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738 eq31694
  have eq173622 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173488
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq173488
    | exact resolve eq173488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173488
  have eq229825 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131399 x
       have i₂ := eq173622
       grind)
    | exact superpose eq173622 eq131399
    | (have j0 := eq131399 x
       grind)
    | (have r₁ := eq131399 x
       have r₂ := eq173622
       grind)
    | exact resolve eq131399 eq173622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173622
  have eq229859 : x ≠ y ∨ x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq131399 x
       grind)
    | (have r₁ := eq229825
       have r₂ := eq131399 x
       grind)
    | exact resolve eq229825 eq131399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131399 eq229825
  have eq229867 : x = (σ (M.op (τ x) (τ x))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq229859
       have r₂ := eq60965
       grind)
    | exact resolve eq229859 eq60965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60965 eq229859
  have eq230637 : x = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3099 x x
       have i₂ := eq229867
       grind)
    | exact superpose eq229867 eq3099
    | (have j0 := eq3099 x x
       grind)
    | exact resolve eq3099 eq229867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq230651 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op (τ x) (τ x))
       have i₂ := eq229867
       grind)
    | exact superpose eq229867 eq9
    | exact resolve eq9 eq229867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229867
  have eq230676 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq230637
  have eq230959 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq230676
       grind)
    | exact superpose eq230676 eq841
    | (have j0 := eq841 x
       grind)
    | exact resolve eq841 eq230676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230676
  have eq230994 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq230959
  have eq232110 : (M.op x x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8475 (τ x) (τ x)
       have i₂ := eq230651
       grind)
    | exact superpose eq230651 eq8475
    | exact resolve eq8475 eq230651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq232129 : (M.op x x) = (M.op (τ x) (τ x)) ∨ y = (M.op x x) := by grind
  clear eq232110
  have eq236709 : (M.op x x) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq230651
       have i₂ := eq232129
       grind)
    | exact superpose eq232129 eq230651
    | exact resolve eq230651 eq232129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230651 eq232129
  have eq236840 : (M.op x x) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq236709
  have eq237212 : ∀ X0 : G, (τ x) = (M.op (τ x) X0) ∨ y = (τ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13317 X0
       have i₂ := eq236840
       grind)
    | exact superpose eq236840 eq13317
    | exact resolve eq13317 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13317
  have eq237213 : (σ x) ≠ (τ x) ∨ y = (τ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15333
       have i₂ := eq236840
       grind)
    | exact superpose eq236840 eq15333
    | exact resolve eq15333 eq236840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15333
  have eq237396 : y ≠ (τ x) ∨ y = (M.op x x) := by grind
  clear eq236840
  have eq237403 : (σ x) ≠ (τ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq237213
       have r₂ := eq237396
       grind)
    | exact resolve eq237213 eq237396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237213
  have eq237404 : ∀ X0 : G, (τ x) = (M.op (τ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq237212 X0
       grind)
    | (have r₁ := eq237212 X0
       have r₂ := eq237396
       grind)
    | exact resolve eq237212 eq237396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237212 eq237396
  have eq239229 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (τ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (τ x) X0 X1
       have i₂ := eq237404 (M.op (τ x) (τ x))
       grind)
    | exact superpose eq237404 eq8
    | exact resolve eq8 eq237404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237404
  have eq250337 : (M.op (σ x) (σ x)) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq239229 (σ x) (σ x)
       have i₂ := eq230994
       grind)
    | exact superpose eq230994 eq239229
    | exact resolve eq239229 eq230994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239229
  have eq250985 : (M.op (σ x) (σ x)) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq250337
  have eq255598 : (σ x) = (τ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq230994
       have i₂ := eq250985
       grind)
    | exact superpose eq250985 eq230994
    | exact resolve eq230994 eq250985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230994 eq250985
  have eq255746 : (σ x) = (τ x) ∨ y = (M.op x x) := by grind
  clear eq255598
  have eq255759 : y = (M.op x x) := by
    first
    | (have r₁ := eq255746
       have r₂ := eq237403
       grind)
    | exact resolve eq255746 eq237403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237403 eq255746
  have eq255944 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq21
    | exact resolve eq21 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq255949 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88 x X0 X1
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq88
    | exact resolve eq88 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq256001 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq758 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq758
    | exact resolve eq758 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq256009 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1268 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq1268
    | exact resolve eq1268 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq256030 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq35131 X0 x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq35131
    | (have j0 := eq35131 X0 x
       grind)
    | exact resolve eq35131 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256046 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq8
    | exact resolve eq8 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq18
    | exact resolve eq18 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq256060 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op y x) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq139 X0 X1 X2 x x X3
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq139
    | exact resolve eq139 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq256223 : ∀ X1 : G, (M.op y x) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq255949 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq255949
    | exact resolve eq255949 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255949
  have eq257232 : ∀ X0 X1 X5 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op x y) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq2774 x x x (M.op (M.op (M.op (M.op x x) x) x) (M.op (M.op (M.op x x) x) x)) X5 X0 X1
       have i₂ := eq255944 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq255944 eq2774
    | exact resolve eq2774 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq257255 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1869 x x x X0 X1 X2 x (M.op (M.op (M.op (M.op (M.op x x) x) x) x) (M.op (M.op (M.op (M.op x x) x) x) x))
       have i₂ := eq255944 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq255944 eq1869
    | exact resolve eq1869 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq257267 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2393 x x x x X0 X1 x (M.op (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x) (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x))
       have i₂ := eq255944 (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x)
       grind)
    | exact superpose eq255944 eq2393
    | exact resolve eq2393 eq255944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393 eq255944
  have eq257275 : ∀ X2 : G, (M.op x y) = (M.op (M.op y x) X2) := by
    intro X2
    first
    | (have i₁ := eq257255 x x X2
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq257255
    | exact resolve eq257255 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257255
  have eq257287 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq257232 X0 X1 x
       have i₂ := eq256223 x
       grind)
    | exact superpose eq256223 eq257232
    | exact resolve eq257232 eq256223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256223 eq257232
  have eq257755 : ∀ X1 : G, (M.op y x) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq257287 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq257287
    | exact resolve eq257287 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257287
  have eq257998 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq257755 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq257755
    | exact resolve eq257755 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257755
  have eq258917 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36096 (M.op x y) X0 X2 x
       have i₂ := eq256001 X0
       grind)
    | exact superpose eq256001 eq36096
    | exact resolve eq36096 eq256001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36096 eq256001
  have eq258961 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq258917 X0 x x
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq258917
    | (have j0 := eq258917 X0 x x
       grind)
    | exact resolve eq258917 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258917
  have eq258967 : ∀ X0 : G, (M.op x y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq258961 X0
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq258961
    | (have j0 := eq258961 X0
       grind)
    | exact resolve eq258961 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258961
  have eq261568 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y x) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq256048 X1 (M.op X1 X1)
       have i₂ := eq35131 X0 X1
       grind)
    | (have i₁ := eq256048 X0 X1
       have i₂ := eq35131 (M.op X0 X1) X1
       grind)
    | exact superpose eq35131 eq256048
    | (have j1 := eq35131 X0 X1
       grind)
    | exact resolve eq256048 eq35131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35131
  have eq262986 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x y) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261568 X0 X1
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq261568
    | (have j0 := eq261568 X0 X1
       grind)
    | exact resolve eq261568 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261568
  have eq291748 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq256009 (σ (M.op x y))
       have i₂ := eq256030 (σ (M.op x y))
       grind)
    | exact superpose eq256030 eq256009
    | (have j1 := eq256030 (σ (M.op x y))
       grind)
    | exact resolve eq256009 eq256030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256009 eq256030
  have eq291782 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq258967 (M.op x y)
       grind)
    | (have r₁ := eq291748
       have r₂ := eq258967 x
       grind)
    | exact resolve eq291748 eq258967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258967 eq291748
  have eq361155 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1 (σ (M.op x y)) (σ (M.op x y))
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq87
    | exact resolve eq87 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq361241 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq256060 (σ (M.op x y)) (σ (M.op x y)) X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq256060
    | exact resolve eq256060 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256060
  have eq361247 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op y x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361241 X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq361241
    | exact resolve eq361241 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361241
  have eq361288 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361155 X0 X1
       have i₂ := eq291782
       grind)
    | exact superpose eq291782 eq361155
    | exact resolve eq361155 eq291782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291782 eq361155
  have eq361372 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq361247 X0 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq361247
    | exact resolve eq361247 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361247
  have eq361397 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq361288 x X1
       have i₂ := eq256046 x
       grind)
    | exact superpose eq256046 eq361288
    | exact resolve eq361288 eq256046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256046 eq361288
  have eq361471 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq361397 x
       have i₂ := eq257275 x
       grind)
    | exact superpose eq257275 eq361397
    | exact resolve eq361397 eq257275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257275 eq361397
  have eq362090 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq361471
       grind)
    | exact superpose eq361471 eq9
    | exact resolve eq9 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363907 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq3900 (σ (M.op x y))
       have i₂ := eq361372 (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact superpose eq361372 eq3900
    | exact resolve eq3900 eq361372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3900 eq361372
  have eq363969 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq363907
       have r₂ := eq361471
       grind)
    | exact resolve eq363907 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363907
  have eq364243 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq363969
       have i₂ := eq10791
       grind)
    | exact superpose eq10791 eq363969
    | exact resolve eq363969 eq10791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791 eq363969
  have eq364647 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq14
    | exact resolve eq14 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364924 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq257267 (σ x) (σ y)
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq257267
    | exact resolve eq257267 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257267
  have eq365123 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq364647
       have i₂ := eq361471
       grind)
    | exact superpose eq361471 eq364647
    | exact resolve eq364647 eq361471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364647
  have eq365416 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq365123
       have i₂ := eq262986 X0 X1
       grind)
    | (have i₁ := eq365123
       have i₂ := eq262986 x y
       grind)
    | exact superpose eq262986 eq365123
    | (have j1 := eq262986 X0 X1
       grind)
    | exact resolve eq365123 eq262986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262986
  have eq365941 : (M.op x y) = (σ x) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq6241 x
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq6241
    | (have j0 := eq6241 x
       grind)
    | exact resolve eq6241 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6241
  have eq365970 : (k (τ (σ x)) x) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq67 (σ x) x
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq67
    | exact resolve eq67 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq366595 : (k (τ (σ x)) x) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq365970
       have r₂ := eq365123
       grind)
    | exact resolve eq365970 eq365123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365970
  have eq366607 : (M.op x x) = (k x x) := by
    first
    | (have j1 := eq365416 x x
       grind)
    | (have r₁ := eq365941
       have r₂ := eq365416 x y
       grind)
    | exact resolve eq365941 eq365416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365416 eq365941
  have eq366730 : (M.op x y) = (k (τ (σ x)) x) := by
    first
    | (have i₁ := eq366595
       have i₂ := eq362090
       grind)
    | exact superpose eq362090 eq366595
    | exact resolve eq366595 eq362090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362090 eq366595
  have eq366735 : y = (k x x) := by
    first
    | (have i₁ := eq366607
       have i₂ := eq255759
       grind)
    | exact superpose eq255759 eq366607
    | exact resolve eq366607 eq255759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255759 eq366607
  have eq366815 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq366730
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq366730
    | exact resolve eq366730 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366730
  have eq366868 : y = (M.op x y) := by
    first
    | (have i₁ := eq366815
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq366815
    | exact resolve eq366815 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366815
  have eq367410 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq841
    | (have j0 := eq841 x
       grind)
    | exact resolve eq841 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq367497 : (M.op x y) = (σ x) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq367410
       have i₂ := eq364924
       grind)
    | exact superpose eq364924 eq367410
    | exact resolve eq367410 eq364924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364924 eq367410
  have eq367508 : (σ x) ≠ (σ y) := by
    first
    | (have r₁ := eq367497
       have r₂ := eq365123
       grind)
    | exact resolve eq367497 eq365123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367497
  have eq367938 : y = (σ y) := by
    first
    | (have i₁ := eq361471
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq361471
    | exact resolve eq361471 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361471
  have eq367940 : y ≠ (σ x) := by
    first
    | (have i₁ := eq365123
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq365123
    | exact resolve eq365123 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365123
  have eq368701 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq364243
       have i₂ := eq367938
       grind)
    | exact superpose eq367938 eq364243
    | exact resolve eq364243 eq367938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367938
  have eq375721 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ y)) X2) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4758 x X1 X2 x
       have i₂ := eq366735
       grind)
    | exact superpose eq366735 eq4758
    | exact resolve eq4758 eq366735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758 eq366735
  have eq375925 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq375721 X0 X1 X2
       grind)
    | (have r₁ := eq375721 X0 X1 X2
       have r₂ := eq367508
       grind)
    | exact resolve eq375721 eq367508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367508 eq375721
  have eq375939 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375925 X0 X1 X2
       have i₂ := eq364243
       grind)
    | exact superpose eq364243 eq375925
    | exact resolve eq375925 eq364243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364243 eq375925
  have eq375943 : ∀ X2 : G, (M.op y x) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375939 x x X2
       have i₂ := eq256048 x x
       grind)
    | exact superpose eq256048 eq375939
    | exact resolve eq375939 eq256048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256048 eq375939
  have eq375944 : ∀ X2 : G, (M.op x y) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375943 X2
       have i₂ := eq257998
       grind)
    | exact superpose eq257998 eq375943
    | exact resolve eq375943 eq257998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257998 eq375943
  have eq375945 : ∀ X2 : G, y = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq375944 X2
       have i₂ := eq366868
       grind)
    | exact superpose eq366868 eq375944
    | exact resolve eq375944 eq366868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366868 eq375944
  have eq376225 : y = (σ x) := by
    first
    | (have i₁ := eq368701
       have i₂ := eq375945 y
       grind)
    | exact superpose eq375945 eq368701
    | exact resolve eq368701 eq375945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368701 eq375945
  have eq377518 : False := by grind
  exact eq377518

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4393 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4393 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op x X3) X3
       have i₂ := eq8 X0 x X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq8 X1 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
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
  clear eq17
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op x X5) X5
       have i₂ := eq18 x X5 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op x X5) X5
       have i₂ := eq18 X0 X1 x X5
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op X0 (M.op X0 X0)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq18 X1 X2 (M.op x X4) X4
       have i₂ := eq8 X0 x X4
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq133 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X3 (M.op X3 X3)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq20 X3 x X4
       have i₂ := eq20 X0 x X1
       grind)
    | (have i₁ := eq20 X0 (M.op X0 (M.op X0 X0)) X3
       have i₂ := eq20 X0 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op X1 X1)) ∨ (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 (M.op X1 (M.op X1 X1)) X2
       have i₂ := eq20 X1 X0 X2
       grind)
    | (have i₁ := eq111 X1 (M.op X1 X1)
       have i₂ := eq20 X0 X1 x
       grind)
    | exact superpose eq20 eq111
    | (have j0 := eq111 (M.op X1 (M.op X1 X1)) X2
       grind)
    | (have r₁ := eq111 (M.op (M.op X0 (M.op X0 X0)) x) (M.op (M.op (M.op X0 (M.op X0 X0)) x) (M.op (M.op X0 (M.op X0 X0)) x))
       have r₂ := eq20 X0 (M.op (M.op X0 (M.op X0 X0)) x) x
       grind)
    | (have r₁ := eq111 (M.op X1 (M.op X1 X1)) x
       have r₂ := eq20 X1 X1 x
       grind)
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq189 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X1 X2
    first
    | (have j0 := eq188 x X1 X2
       grind)
    | (have r₁ := eq188 x X1 X2
       have r₂ := eq21 x X1
       grind)
    | (have r₁ := eq188 X1 x X2
       have r₂ := eq21 x X1
       grind)
    | exact resolve eq188 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq580 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) X3) ∨ (M.op (M.op X2 X3) X3) = (k (M.op (M.op X2 X3) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111 (M.op (M.op X2 X3) X3) X4
       have i₂ := eq55 X2 X3 X0 X1 X4
       grind)
    | (have i₁ := eq111 (M.op X2 X3) X3
       have i₂ := eq55 X0 X1 X2 X3 x
       grind)
    | exact superpose eq55 eq111
    | (have j0 := eq111 (M.op (M.op X2 X3) X3) X4
       grind)
    | (have r₁ := eq111 (M.op (M.op (M.op X0 X1) X1) x) x
       have r₂ := eq55 X0 X1 (M.op (M.op X0 X1) X1) x x
       grind)
    | (have r₁ := eq111 (M.op (M.op X2 X3) X3) x
       have r₂ := eq55 X2 X3 X2 X3 x
       grind)
    | exact resolve eq111 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq581 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X3) = (k (M.op (M.op X2 X3) X3) X4) := by
    intro X2 X3 X4
    first
    | (have j0 := eq580 x x X2 X3 X4
       grind)
    | (have r₁ := eq580 x x X3 X4 X4
       have r₂ := eq18 x x X3 X4
       grind)
    | (have r₁ := eq580 X3 X4 x x X4
       have r₂ := eq18 x x X3 X4
       grind)
    | exact resolve eq580 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq760 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq817 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1831 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq1935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1831 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1831
    | (have j0 := eq1831 X0 X1
       grind)
    | exact resolve eq1831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq2015 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2572 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 (M.op X2 X2)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq77 (σ X1) X2 X0
       grind)
    | exact superpose eq77 eq26
    | (have j1 := eq77 (σ X1) X2 X0
       grind)
    | exact resolve eq26 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq77
  have eq6106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq760
       have i₂ := eq2015 y x
       grind)
    | exact superpose eq2015 eq760
    | (have j1 := eq2015 y x
       grind)
    | (have r₁ := eq760
       have r₂ := eq2015 y x
       grind)
    | exact resolve eq760 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq6107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq760
       have i₂ := eq1935 y x
       grind)
    | exact superpose eq1935 eq760
    | (have j1 := eq1935 (σ y) (σ x)
       grind)
    | (have r₁ := eq760
       have r₂ := eq1935 y x
       grind)
    | exact resolve eq760 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1935
  have eq6108 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6107
  have eq6109 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq6106
  have eq6121 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq6108
       grind)
    | exact superpose eq6108 eq133
    | exact resolve eq133 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6175 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6121
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6121
    | exact resolve eq6121 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6281 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6175
       grind)
    | exact superpose eq6175 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6175
  have eq6286 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6281
  have eq6755 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x y
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq8
    | exact resolve eq8 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6757 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x y
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq18
    | exact resolve eq18 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6768 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq581 x y x
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq581
    | exact resolve eq581 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq8612 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq133 x
       have i₂ := eq6109
       grind)
    | exact superpose eq6109 eq133
    | exact resolve eq133 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6109
  have eq8677 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8612
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8612
    | exact resolve eq8612 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8678 : x = (k x y) := by grind
  clear eq8677
  have eq10007 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6755 (σ x)
       have i₂ := eq6108
       grind)
    | exact superpose eq6108 eq6755
    | exact resolve eq6755 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108 eq6755
  have eq10139 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq10007
  have eq10736 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq6757 (M.op x X1) X1
       have i₂ := eq6757 x X1
       grind)
    | exact superpose eq6757 eq6757
    | exact resolve eq6757 eq6757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6757
  have eq10895 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq10736 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736
  have eq11466 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6768 X0
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq6768
    | exact resolve eq6768 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6768
  have eq11503 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq11466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466
  have eq11892 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq817 x
       have i₂ := eq11503 x
       grind)
    | exact superpose eq11503 eq817
    | (have j0 := eq817 x
       grind)
    | exact resolve eq817 eq11503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11503
  have eq11917 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq11892
  have eq18765 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq10139
       grind)
    | exact superpose eq10139 eq14
    | exact resolve eq14 eq10139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq19412 : x ≠ (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18765
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq18765
    | exact resolve eq18765 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18765
  have eq19415 : x ≠ (σ x) ∨ y = (M.op x x) := by grind
  clear eq19412
  have eq21828 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10895 x
       have i₂ := eq6286
       grind)
    | exact superpose eq6286 eq10895
    | exact resolve eq10895 eq6286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6286 eq10895
  have eq22060 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21828
  have eq23109 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq22060 (M.op x x)
       grind)
    | exact superpose eq22060 eq21
    | exact resolve eq21 eq22060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060
  have eq24232 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23109 (σ x)
       have i₂ := eq11917
       grind)
    | exact superpose eq11917 eq23109
    | exact resolve eq23109 eq11917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23109
  have eq24452 : x = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq24232
  have eq31833 : x = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11917
       have i₂ := eq24452
       grind)
    | exact superpose eq24452 eq11917
    | exact resolve eq11917 eq24452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11917 eq24452
  have eq31960 : x = (σ x) ∨ y = (M.op x x) := by grind
  clear eq31833
  have eq31965 : y = (M.op x x) := by
    first
    | (have r₁ := eq31960
       have r₂ := eq19415
       grind)
    | exact resolve eq31960 eq19415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19415 eq31960
  have eq32748 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq21
    | exact resolve eq21 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq32762 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq189 x x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq189
    | exact resolve eq189 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq32788 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x x
       have i₂ := eq31965
       grind)
    | exact superpose eq31965 eq8
    | exact resolve eq8 eq31965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31965
  have eq35653 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1 x (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))
       have i₂ := eq32748 (M.op x (M.op x x))
       grind)
    | exact superpose eq32748 eq139
    | exact resolve eq139 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq35663 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x X0 X1 (M.op (M.op (M.op x x) x) (M.op (M.op x x) x))
       have i₂ := eq32748 (M.op (M.op x x) x)
       grind)
    | exact superpose eq32748 eq55
    | exact resolve eq55 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq35686 : ∀ X1 : G, (M.op x y) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq35653 x X1
       have i₂ := eq32788 x
       grind)
    | exact superpose eq32788 eq35653
    | exact resolve eq35653 eq32788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35653
  have eq39276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq817 (M.op x y)
       have i₂ := eq32762 (M.op x y)
       grind)
    | exact superpose eq32762 eq817
    | (have j0 := eq817 (M.op x y)
       grind)
    | exact resolve eq817 eq32762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq32762
  have eq39316 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq39276
  have eq222174 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (σ (M.op x y)) (σ (M.op x y)) X1
       have i₂ := eq39316
       grind)
    | exact superpose eq39316 eq56
    | exact resolve eq56 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq222292 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq222174 X0 X1
       have i₂ := eq39316
       grind)
    | exact superpose eq39316 eq222174
    | exact resolve eq222174 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39316 eq222174
  have eq222427 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op y x) X1) := by
    intro X1
    first
    | (have i₁ := eq222292 x X1
       have i₂ := eq32788 x
       grind)
    | exact superpose eq32788 eq222292
    | exact resolve eq222292 eq32788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32788 eq222292
  have eq222527 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq222427 x
       have i₂ := eq35686 x
       grind)
    | exact superpose eq35686 eq222427
    | exact resolve eq222427 eq35686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35686 eq222427
  have eq249003 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (σ (M.op x y)) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq2572 (σ x) y X0
       grind)
    | exact superpose eq2572 eq14
    | (have j1 := eq2572 (σ x) y x
       grind)
    | exact resolve eq14 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq249009 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op x y) ∨ (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq249003 X0
       have i₂ := eq222527
       grind)
    | exact superpose eq222527 eq249003
    | exact resolve eq249003 eq222527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249003
  have eq249063 : (k (τ (σ x)) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq249009 x
       have r₂ := eq32748 x
       grind)
    | exact resolve eq249009 eq32748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32748 eq249009
  have eq249091 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq249063
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq249063
    | exact resolve eq249063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249063
  have eq249097 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq249091
       have i₂ := eq8678
       grind)
    | exact superpose eq8678 eq249091
    | exact resolve eq249091 eq8678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8678 eq249091
  have eq249150 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq249097
       grind)
    | exact superpose eq249097 eq10
    | exact resolve eq10 eq249097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249097
  have eq249594 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq14
    | exact resolve eq14 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249741 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35663 (σ x) (σ y)
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq35663
    | exact resolve eq35663 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35663
  have eq249745 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq249741
       have i₂ := eq249150
       grind)
    | exact superpose eq249150 eq249741
    | exact resolve eq249741 eq249150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249150 eq249741
  have eq249868 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq249594
       have i₂ := eq222527
       grind)
    | exact superpose eq222527 eq249594
    | exact resolve eq249594 eq222527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222527 eq249594
  have eq249930 : False := by grind
  exact eq249930
