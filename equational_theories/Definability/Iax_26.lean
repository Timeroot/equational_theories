import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4397`: `x ◇ (x ◇ y) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4397 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4397 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4397.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X3) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 x) X3
       have i₂ := eq8 X0 x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 x X3
       have i₂ := eq8 X0 x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X2)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X0) X2 X3
       have i₂ := eq8 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) x X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq112 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) ≠ (M.op (M.op X0 X0) X1) ∨ (k X0 (M.op (M.op X0 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X0) X2)
       have i₂ := eq17 X0 X2 X1
       grind)
    | exact superpose eq17 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X0) X2)
       grind)
    | (have r₁ := eq11 (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X1))
       have r₂ := eq17 X0 X1 (M.op X0 (M.op (M.op X0 X0) X1))
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq17 X0 x x
       grind)
    | exact resolve eq11 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X2 : G, (k X0 (M.op (M.op X0 X0) X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq161 X0 x X2
       grind)
    | (have r₁ := eq161 X0 x x
       have r₂ := eq19 X0 x x
       grind)
    | (have r₁ := eq161 X0 x x
       have r₂ := eq19 X0 x x
       grind)
    | exact resolve eq161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq170 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op (M.op X0 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 x
       have i₂ := eq17 X0 X1 x
       grind)
    | exact superpose eq17 eq165
    | exact resolve eq165 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq165
  have eq210 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq19 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq19 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X3 X2
       have i₂ := eq8 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq21 X0 X1 x X2
       grind)
    | exact superpose eq21 eq170
    | exact resolve eq170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq170
  have eq513 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq976 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq210 X0 X1 X4 (M.op (M.op (M.op X0 X0) X1) x)
       have i₂ := eq210 (M.op (M.op X0 X0) X1) X2 x X3
       grind)
    | exact superpose eq210 eq210
    | exact resolve eq210 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X0 X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq211 X0 x X3 X5
       have i₂ := eq210 X0 X1 x X2
       grind)
    | exact superpose eq210 eq211
    | exact resolve eq211 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq2096 : ∀ X0 X1 X2 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X4))) = X0 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq426 X0 x X4
       have i₂ := eq211 X0 X1 x X2
       grind)
    | exact superpose eq211 eq426
    | exact resolve eq426 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq5345 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq5403 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5345 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5345
    | (have j0 := eq5345 X0 X1
       grind)
    | exact resolve eq5345 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345
  have eq46984 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq513
    | exact resolve eq513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq47190 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46984 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq46984
    | (have j0 := eq46984 X0 X1
       grind)
    | exact resolve eq46984 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46984
  have eq47193 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47190 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq47190
    | (have j0 := eq47190 X0 X1
       grind)
    | exact resolve eq47190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47190
  have eq47195 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47193 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq47193 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq47193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47193
  have eq47211 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47195 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47195
    | exact resolve eq47195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47240 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq47195 (σ X0) X1
       grind)
    | exact superpose eq47195 eq39
    | (have j1 := eq47195 (σ X0) X1
       grind)
    | exact resolve eq39 eq47195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47195
  have eq47314 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47240 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq47240
    | (have j0 := eq47240 X0 X1
       grind)
    | exact resolve eq47240 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47240
  have eq47337 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47314 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47314
    | (have j0 := eq47314 X0 X1
       grind)
    | exact resolve eq47314 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47314
  have eq47345 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47337 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq47337
    | (have j0 := eq47337 X0 X1
       grind)
    | exact resolve eq47337 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47337
  have eq47694 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq47211 X1 (τ X0)
       grind)
    | exact superpose eq47211 eq15
    | (have j1 := eq47211 X1 (τ X0)
       grind)
    | exact resolve eq15 eq47211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq47719 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47694 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47694
    | (have j0 := eq47694 X0 X1
       grind)
    | exact resolve eq47694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47694
  have eq52325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47345 x y
       grind)
    | exact superpose eq47345 eq14
    | (have j1 := eq47345 x y
       grind)
    | exact resolve eq14 eq47345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47345
  have eq52666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq52325
       have i₂ := eq47211 y x
       grind)
    | exact superpose eq47211 eq52325
    | (have j1 := eq47211 y x
       grind)
    | exact resolve eq52325 eq47211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47211 eq52325
  have eq52675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by grind
  clear eq52666
  have eq52676 : x = (k x y) := by grind
  clear eq52675
  have eq53396 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53399 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5403 x y
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq5403
    | (have j0 := eq5403 x y
       grind)
    | exact resolve eq5403 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5403
  have eq56392 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op y (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq211 y x X0 X1
       have i₂ := eq53396
       grind)
    | exact superpose eq53396 eq211
    | exact resolve eq211 eq53396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq70780 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47719 X0 X1
       grind)
    | exact superpose eq47719 eq16
    | (have j1 := eq47719 X0 X1
       grind)
    | exact resolve eq16 eq47719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq47719
  have eq141628 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70780 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq70780
    | (have j0 := eq70780 (σ X0) X1
       grind)
    | exact resolve eq70780 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70780
  have eq141660 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141628 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq141628
    | (have j0 := eq141628 X0 X1
       grind)
    | exact resolve eq141628 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141628
  have eq141663 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141660 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq141660
    | (have j0 := eq141660 X0 X1
       grind)
    | exact resolve eq141660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141660
  have eq145919 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq542 X0
       have i₂ := eq141663 X0 X0
       grind)
    | exact superpose eq141663 eq542
    | (have j0 := eq542 X0
       have j1 := eq141663 X0 X0
       grind)
    | (have r₁ := eq542 x
       have r₂ := eq141663 x x
       grind)
    | exact resolve eq542 eq141663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141663
  have eq145949 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq145919 X0
       have j1 := eq542 X0
       grind)
    | (have r₁ := eq145919 X0
       have r₂ := eq542 X0
       grind)
    | exact resolve eq145919 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145919
  have eq163661 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56392 x x
       have i₂ := eq53396
       grind)
    | exact superpose eq53396 eq56392
    | exact resolve eq56392 eq53396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56392
  have eq163947 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq163661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163661
  have eq164151 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53396
       have i₂ := eq163947 X0
       grind)
    | exact superpose eq163947 eq53396
    | exact resolve eq53396 eq163947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53396
  have eq164152 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53399
       have i₂ := eq163947 X0
       grind)
    | exact superpose eq163947 eq53399
    | exact resolve eq53399 eq163947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53399 eq163947
  have eq164569 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq164152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164152
  have eq164570 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq164151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164151
  have eq165419 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2096 x x x x
       have i₂ := eq164570 (M.op (M.op (M.op x (M.op x x)) x) x)
       grind)
    | exact superpose eq164570 eq2096
    | exact resolve eq2096 eq164570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096 eq164570
  have eq166521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq542 x
       have i₂ := eq165419
       grind)
    | exact superpose eq165419 eq542
    | (have j0 := eq542 x
       grind)
    | exact resolve eq542 eq165419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq165419
  have eq166540 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq166521
  have eq170999 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ x) X1 x
       have i₂ := eq166540
       grind)
    | exact superpose eq166540 eq19
    | exact resolve eq19 eq166540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq188369 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq166540
       have i₂ := eq170999 (σ x) X0
       grind)
    | (have i₁ := eq166540
       have i₂ := eq170999 X0 (σ x)
       grind)
    | exact superpose eq170999 eq166540
    | exact resolve eq166540 eq170999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166540 eq170999
  have eq188500 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq188369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188369
  have eq188604 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq188500 (σ y)
       grind)
    | exact superpose eq188500 eq14
    | exact resolve eq14 eq188500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188500
  have eq188859 : y = (M.op x y) := by
    first
    | (have r₁ := eq188604
       have r₂ := eq164569 y
       grind)
    | exact resolve eq188604 eq164569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164569 eq188604
  have eq188901 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x X0 y
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq22
    | exact resolve eq22 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq189101 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq188901 X0
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq188901
    | exact resolve eq188901 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188901
  have eq192007 : ∀ X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op (M.op x x) X1) (M.op (M.op x x) X1)) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq976 x X1 X2 X3 x
       have i₂ := eq189101 x
       grind)
    | exact superpose eq189101 eq976
    | exact resolve eq976 eq189101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq192023 : ∀ X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op x x) X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1181 x X1 X2 x X3
       have i₂ := eq189101 x
       grind)
    | exact superpose eq189101 eq1181
    | exact resolve eq1181 eq189101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq189101
  have eq192384 : ∀ X3 : G, y = (M.op y X3) := by
    intro X3
    first
    | (have i₁ := eq192007 x x X3
       have i₂ := eq192023 x (M.op (M.op x x) x) x
       grind)
    | exact superpose eq192023 eq192007
    | exact resolve eq192007 eq192023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192007 eq192023
  have eq192848 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq145949 y
       have i₂ := eq192384 y
       grind)
    | exact superpose eq192384 eq145949
    | (have j0 := eq145949 y
       grind)
    | exact resolve eq145949 eq192384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145949
  have eq193310 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq192848
  have eq195862 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ y) x (σ y)
       have i₂ := eq193310
       grind)
    | exact superpose eq193310 eq23
    | exact resolve eq23 eq193310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq195970 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq195862 X0
       have i₂ := eq193310
       grind)
    | exact superpose eq193310 eq195862
    | exact resolve eq195862 eq193310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193310 eq195862
  have eq196668 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq112 (σ y) X0
       have i₂ := eq195970 (σ X0)
       grind)
    | exact superpose eq195970 eq112
    | (have j0 := eq112 (σ y) X0
       grind)
    | exact resolve eq112 eq195970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq196686 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq196668 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq196668
    | (have j0 := eq196668 X0
       grind)
    | exact resolve eq196668 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196668
  have eq319599 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq196686 x
       grind)
    | exact superpose eq196686 eq14
    | (have j1 := eq196686 x
       grind)
    | exact resolve eq14 eq196686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196686
  have eq319684 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq319599
       have i₂ := eq188859
       grind)
    | exact superpose eq188859 eq319599
    | exact resolve eq319599 eq188859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188859 eq319599
  have eq319685 : y = (k x y) := by grind
  clear eq319684
  have eq319686 : x = y := by
    first
    | (have i₁ := eq319685
       have i₂ := eq52676
       grind)
    | exact superpose eq52676 eq319685
    | exact resolve eq319685 eq52676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52676 eq319685
  have eq319689 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq14
    | exact resolve eq14 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319862 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq192384 x
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq192384
    | exact resolve eq192384 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192384
  have eq319932 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq195970 X0
       have i₂ := eq319686
       grind)
    | exact superpose eq319686 eq195970
    | exact resolve eq195970 eq319686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195970 eq319686
  have eq320098 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq319689
       have i₂ := eq319862 x
       grind)
    | exact superpose eq319862 eq319689
    | exact resolve eq319689 eq319862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319689 eq319862
  have eq320179 : False := by grind
  exact eq320179

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4400 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4400 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) x x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq8 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 X3
       have i₂ := eq8 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 (M.op (M.op X0 X1) X3) X2
       grind)
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 X2 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq19 X0 X1 X2 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2 x
       grind)
    | (have r₁ := eq228 X0 X1 x x
       have r₂ := eq60 X0 X1 x x x
       grind)
    | exact resolve eq228 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq277 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 (M.op X0 X1) x
       have i₂ := eq24 X0 X1 x
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq236 (M.op X0 X1) x x
       have i₂ := eq21 X0 X1 x x
       grind)
    | exact superpose eq21 eq236
    | exact resolve eq236 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq236
  have eq323 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq277 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq277
    | exact resolve eq277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (M.op (σ X0) X1))
       have i₂ := eq277 (σ X0) X1
       grind)
    | exact superpose eq277 eq38
    | exact resolve eq38 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq343 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq339
    | exact resolve eq339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq422 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq425 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) X2) = (M.op (σ (k X0 X1)) X3) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X0) (σ X1) X2 X3
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq17
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X3 x
       have i₂ := eq60 X0 X1 X2 X3 x
       grind)
    | exact superpose eq60 eq19
    | exact resolve eq19 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq60
  have eq821 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2580 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 (τ X0) (τ X1)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq434
    | (have j0 := eq434 (τ X0) (τ X1)
       grind)
    | exact resolve eq434 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2587 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2580 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2580
    | (have j0 := eq2580 X0 X1
       grind)
    | exact resolve eq2580 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq2592 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2587 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2587
    | (have j0 := eq2587 X0 X1
       grind)
    | exact resolve eq2587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2596 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2592 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2592
    | (have j0 := eq2592 X0 X1
       grind)
    | exact resolve eq2592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2597 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2596 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2596
    | (have j0 := eq2596 X0 X1
       grind)
    | exact resolve eq2596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2625 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (τ X0) X1) X2)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X1) = (M.op (M.op (τ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 (M.op (τ X0) X1)
       have i₂ := eq8 (τ X0) X1 X2
       grind)
    | exact superpose eq8 eq31
    | exact resolve eq31 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq422
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq422
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq422 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4566 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4565
  have eq4572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) (σ y) x
       have i₂ := eq4566
       grind)
    | exact superpose eq4566 eq8
    | exact resolve eq8 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4573 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq4566
       grind)
    | exact superpose eq4566 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq4566
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq4566
       grind)
    | exact resolve eq11 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq4600 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4573
  have eq4607 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4600
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4600
    | exact resolve eq4600 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq4832 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4607
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq4607
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq4607 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4835 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq4607
       grind)
    | exact superpose eq4607 eq9
    | exact resolve eq9 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607
  have eq4856 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4832
  have eq4870 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4835
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4835
    | exact resolve eq4835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq4871 : x = (k x y) := by
    first
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq4870
       have r₂ := eq11 x y
       grind)
    | exact resolve eq4870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq5416 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq422
    | exact resolve eq422 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq5419 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6191 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 x y x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq8
    | exact resolve eq8 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6193 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 x y x x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq17
    | exact resolve eq17 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6215 : y = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq279 x y
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq279
    | exact resolve eq279 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq6222 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op y X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq553 x y x x
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq553
    | exact resolve eq553 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq6224 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq8135 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ (k X0 X1))) X2) = (M.op (σ (τ (k X0 X1))) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq425 (τ X1) (τ X0) X2 X3
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq425
    | (have j0 := eq425 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq425 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq8138 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 x y x x
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq425
    | (have j0 := eq425 x y x x
       grind)
    | exact resolve eq425 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq8302 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8135 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8135
    | (have j0 := eq8135 X0 X1 X2 X3
       grind)
    | exact resolve eq8135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8135
  have eq8308 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8302 X0 X0 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8302
    | (have j0 := eq8302 X0 X1 X2 X3
       grind)
    | exact resolve eq8302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq8309 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) X2) = (M.op (k X0 X1) X3) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8308 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8308
    | (have j0 := eq8308 X0 X1 X2 X3
       grind)
    | exact resolve eq8308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308
  have eq8753 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6215
       have i₂ := eq5419
       grind)
    | exact superpose eq5419 eq6215
    | exact resolve eq6215 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419 eq6215
  have eq8760 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8753
       have r₂ := eq6224
       grind)
    | exact resolve eq8753 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224 eq8753
  have eq9608 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq8760
       grind)
    | exact superpose eq8760 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8760
  have eq9609 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq9608
  have eq9817 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6193 y X0
       have i₂ := eq9609
       grind)
    | exact superpose eq9609 eq6193
    | exact resolve eq6193 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193 eq9609
  have eq9862 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817
  have eq12680 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9862 x
       have i₂ := eq6222 x X0
       grind)
    | exact superpose eq6222 eq9862
    | exact resolve eq9862 eq6222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222 eq9862
  have eq12787 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680
  have eq13029 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12787 x
       have i₂ := eq6191 x
       grind)
    | exact superpose eq6191 eq12787
    | exact resolve eq12787 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191 eq12787
  have eq13086 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq13029
  have eq33480 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq4572 X0
       grind)
    | exact superpose eq4572 eq14
    | exact resolve eq14 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36950 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33480 X0
       have i₂ := eq4856
       grind)
    | exact superpose eq4856 eq33480
    | exact resolve eq33480 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856 eq33480
  have eq36984 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36950 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36950
  have eq37409 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36984 x
       have i₂ := eq4572 x
       grind)
    | exact superpose eq4572 eq36984
    | exact resolve eq36984 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572 eq36984
  have eq37441 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37409
  have eq56808 : ∀ X0 X1 X2 : G, (τ (σ (k X0 (k (τ X1) X2)))) = (k X0 (τ (M.op X1 (σ X2)))) ∨ (σ X2) = (M.op X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (σ X2))
       have i₂ := eq821 X1 X2 X0
       grind)
    | exact superpose eq821 eq38
    | (have j1 := eq821 X1 X2 X2
       grind)
    | exact resolve eq38 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq56847 : ∀ X0 X1 X2 : G, (k X0 (k (τ X1) X2)) = (k X0 (τ (M.op X1 (σ X2)))) ∨ (σ X2) = (M.op X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56808 X0 X1 X2
       have i₂ := eq9 (k X0 (k (τ X1) X2))
       grind)
    | exact superpose eq9 eq56808
    | (have j0 := eq56808 X0 X1 X2
       grind)
    | exact resolve eq56808 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56808
  have eq113921 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq2625 (σ X0) X1 X2
       grind)
    | exact superpose eq2625 eq38
    | (have j1 := eq2625 (σ X0) X1 X2
       grind)
    | exact resolve eq38 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2625
  have eq114041 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) X2))) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113921 X0 X1 X2
       have i₂ := eq9 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq9 eq113921
    | (have j0 := eq113921 X0 X1 X2
       grind)
    | exact resolve eq113921 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113921
  have eq114146 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = (τ (σ (M.op (M.op X0 X1) X2))) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114041 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114041
    | (have j0 := eq114041 X0 X1 X2
       grind)
    | exact resolve eq114041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114041
  have eq114201 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X0 (M.op X0 X1)) ∨ (M.op (τ (σ X0)) X1) = (M.op (M.op (τ (σ X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114146 X0 X1 X2
       have i₂ := eq9 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq9 eq114146
    | (have j0 := eq114146 X0 X1 X2
       grind)
    | exact resolve eq114146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114146
  have eq114219 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114201 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq114201
    | (have j0 := eq114201 X0 X1 X2
       grind)
    | exact resolve eq114201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114201
  have eq138455 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8309 x y x x
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq8309
    | (have j0 := eq8309 x y x x
       grind)
    | exact resolve eq8309 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8309
  have eq140154 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13086
       have i₂ := eq138455 y x
       grind)
    | (have i₁ := eq13086
       have i₂ := eq138455 X0 y
       grind)
    | exact superpose eq138455 eq13086
    | exact resolve eq13086 eq138455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq140458 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    grind
  clear eq138455
  have eq140549 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq140154 X0
       grind)
    | (have r₁ := eq140154 X0
       have r₂ := eq140458 (M.op x X0)
       grind)
    | (have r₁ := eq140154 X0
       have r₂ := eq140458 y
       grind)
    | exact resolve eq140154 eq140458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140154 eq140458
  have eq143729 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq323 x x x x
       have i₂ := eq140549 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq140549 eq323
    | exact resolve eq323 eq140549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq140549
  have eq149782 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq434 x x
       have i₂ := eq143729
       grind)
    | exact superpose eq143729 eq434
    | (have j0 := eq434 x x
       grind)
    | exact resolve eq434 eq143729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq143729
  have eq149803 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq149782
  have eq214574 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ x) (σ x) x x
       have i₂ := eq149803
       grind)
    | exact superpose eq149803 eq17
    | exact resolve eq17 eq149803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq320387 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37441
       have i₂ := eq214574 (σ y) X0
       grind)
    | (have i₁ := eq37441
       have i₂ := eq214574 X0 (σ y)
       grind)
    | exact superpose eq214574 eq37441
    | exact resolve eq37441 eq214574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441
  have eq320391 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq149803
       have i₂ := eq214574 (σ x) X0
       grind)
    | (have i₁ := eq149803
       have i₂ := eq214574 X0 (σ x)
       grind)
    | exact superpose eq214574 eq149803
    | exact resolve eq149803 eq214574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149803 eq214574
  have eq320531 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq320391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320391
  have eq320534 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq320387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320387
  have eq320582 : y = (M.op x y) := by
    first
    | (have r₁ := eq320534 x
       have r₂ := eq320531 x
       grind)
    | exact resolve eq320534 eq320531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320531 eq320534
  have eq828091 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq8138 X0 X1
       grind)
    | exact superpose eq8138 eq14
    | (have j1 := eq8138 X0 X1
       grind)
    | exact resolve eq14 eq8138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8138
  have eq828228 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq828091 X0 X1
       have i₂ := eq320582
       grind)
    | exact superpose eq320582 eq828091
    | (have j0 := eq828091 X0 X1
       grind)
    | exact resolve eq828091 eq320582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828091
  have eq828229 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq828228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828228
  have eq829161 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq343 x x
       have i₂ := eq828229 (M.op (σ x) x) X0
       grind)
    | (have i₁ := eq343 x x
       have i₂ := eq828229 X0 (M.op (σ x) x)
       grind)
    | exact superpose eq828229 eq343
    | exact resolve eq343 eq828229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq829189 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq828229 (σ y) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq828229 X0 (σ y)
       grind)
    | exact superpose eq828229 eq14
    | exact resolve eq14 eq828229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828229
  have eq829625 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq829189 X0
       have i₂ := eq320582
       grind)
    | exact superpose eq320582 eq829189
    | exact resolve eq829189 eq320582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320582 eq829189
  have eq830280 : ∀ X0 : G, x = (k x (k (τ (σ x)) X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56847 x (σ x) X0
       have i₂ := eq829161 (σ X0)
       grind)
    | exact superpose eq829161 eq56847
    | (have j0 := eq56847 X0 (σ x) X0
       grind)
    | exact resolve eq56847 eq829161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56847 eq829161
  have eq830363 : ∀ X0 : G, x = (k x (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq830280 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq830280
    | (have j0 := eq830280 X0
       grind)
    | exact resolve eq830280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830280
  have eq843011 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq830363 y
       have i₂ := eq4871
       grind)
    | exact superpose eq4871 eq830363
    | (have j0 := eq830363 y
       grind)
    | exact resolve eq830363 eq4871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4871 eq830363
  have eq843038 : x = (k x x) := by
    first
    | (have r₁ := eq843011
       have r₂ := eq829625 (σ y)
       grind)
    | exact resolve eq843011 eq829625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843011
  have eq843093 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2597 x x
       have i₂ := eq843038
       grind)
    | exact superpose eq843038 eq2597
    | (have j0 := eq2597 x x
       grind)
    | (have r₁ := eq2597 x x
       have r₂ := eq843038
       grind)
    | exact resolve eq2597 eq843038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq843180 : x = (M.op x x) := by grind
  clear eq843093
  have eq843629 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq114219 x x x
       have i₂ := eq843180
       grind)
    | exact superpose eq843180 eq114219
    | exact resolve eq114219 eq843180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114219 eq843180
  have eq843734 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq843629 X0
       have i₂ := eq843038
       grind)
    | exact superpose eq843038 eq843629
    | (have j0 := eq843629 X0
       grind)
    | exact resolve eq843629 eq843038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843038 eq843629
  have eq843735 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq843734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843734
  have eq844356 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5416
       have i₂ := eq843735 y
       grind)
    | exact superpose eq843735 eq5416
    | exact resolve eq5416 eq843735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416 eq843735
  have eq844936 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq844356
  have eq845155 : False := by grind
  exact eq845155

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4400 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 (M.op X0 X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) x x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 X3
       have i₂ := eq8 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 (M.op (M.op X0 X1) X3) X2
       grind)
    | (have i₁ := eq8 (M.op X0 X1) X3 X4
       have i₂ := eq17 X0 X1 X2 (M.op (M.op X0 X1) X3)
       grind)
    | exact superpose eq17 eq8
    | exact resolve eq8 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have r₂ := eq19 X0 X1 X2 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq228 X0 X1 X2 x
       grind)
    | (have r₁ := eq228 X0 X1 x x
       have r₂ := eq60 X0 X1 x x x
       grind)
    | exact resolve eq228 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq228
  have eq277 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 (M.op X0 X1) x
       have i₂ := eq24 X0 X1 x
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq323 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq277 X0 (M.op (M.op X0 X1) X2)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq277
    | exact resolve eq277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq339 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) (M.op (σ X0) X1))
       have i₂ := eq277 (σ X0) X1
       grind)
    | exact superpose eq277 eq38
    | exact resolve eq38 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq343 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq339
    | exact resolve eq339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq431 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq30 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq11 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) (σ X0) X2
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq8
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq8 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq30 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq11 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq457 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq459 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq433
    | (have j0 := eq433 X0 X1
       grind)
    | exact resolve eq433 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq2622 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2622 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2622
    | (have j0 := eq2622 X0 X1
       grind)
    | exact resolve eq2622 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622
  have eq4653 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq457
    | exact resolve eq457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4660 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq14
    | (have j1 := eq457 x y
       grind)
    | exact resolve eq14 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq4697 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4653 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4653
    | (have j0 := eq4653 X0 X1
       grind)
    | exact resolve eq4653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653
  have eq4699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4697 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4697
    | (have j0 := eq4697 X0 X1
       grind)
    | exact resolve eq4697 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq7569 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4699 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4699
    | exact resolve eq4699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq7821 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7569 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7569
  have eq8519 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X2
       have i₂ := eq443 X0 X2 X1
       grind)
    | (have i₁ := eq30 X0 X0
       have i₂ := eq443 X0 X1 (σ X0)
       grind)
    | exact superpose eq443 eq30
    | (have j0 := eq30 X0 X2
       have j1 := eq443 X0 X2 X2
       grind)
    | exact resolve eq30 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq443
  have eq8699 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq8519 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8519
  have eq13182 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq459 (τ X0) (τ X1)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq459
    | (have j0 := eq459 (τ X0) (τ X1)
       grind)
    | exact resolve eq459 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq459
  have eq13212 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13182 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq13182
    | (have j0 := eq13182 X0 X1
       grind)
    | exact resolve eq13182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13182
  have eq13224 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13212 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13212
    | (have j0 := eq13212 X0 X1
       grind)
    | exact resolve eq13212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212
  have eq13232 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13224 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq13224
    | (have j0 := eq13224 X0 X1
       grind)
    | exact resolve eq13224 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13224
  have eq13235 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13232 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13232
    | (have j0 := eq13232 X0 X1
       grind)
    | exact resolve eq13232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13232
  have eq13236 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13235 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13235
    | (have j0 := eq13235 X0 X1
       grind)
    | exact resolve eq13235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13237 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13236 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13236
    | (have j0 := eq13236 X0 X1
       grind)
    | exact resolve eq13236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13238 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13237 X0 X1
       have j1 := eq7821 X1 X0
       grind)
    | (have r₁ := eq13237 X1 X0
       have r₂ := eq7821 X0 X1
       grind)
    | (have r₁ := eq13237 X0 X1
       have r₂ := eq7821 X0 X1
       grind)
    | exact resolve eq13237 eq7821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7821 eq13237
  have eq13262 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13238 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq13238
    | (have j0 := eq13238 (σ X0) (σ X1)
       grind)
    | exact resolve eq13238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13238
  have eq13293 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13262 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq13262
    | (have j0 := eq13262 X0 X1
       grind)
    | exact resolve eq13262 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13262
  have eq18343 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq431
    | exact resolve eq431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq18457 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18343 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq18343
    | (have j0 := eq18343 X0 X1
       grind)
    | exact resolve eq18343 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq18343
  have eq18459 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18457 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18457
    | (have j0 := eq18457 X0 X1
       grind)
    | exact resolve eq18457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq18457
  have eq18461 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18459 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq18459 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq18459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18459
  have eq18477 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18461 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18461
    | exact resolve eq18461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18507 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq18461 (σ X0) X1
       grind)
    | exact superpose eq18461 eq38
    | (have j1 := eq18461 (σ X0) X1
       grind)
    | exact resolve eq38 eq18461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq18461
  have eq18579 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18507 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq18507
    | (have j0 := eq18507 X0 X1
       grind)
    | exact resolve eq18507 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18507
  have eq18602 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18579 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq18579
    | (have j0 := eq18579 X0 X1
       grind)
    | exact resolve eq18579 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq18610 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18602 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq18602
    | (have j0 := eq18602 X0 X1
       grind)
    | exact resolve eq18602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq20776 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18610 x y
       grind)
    | exact superpose eq18610 eq14
    | (have j1 := eq18610 x y
       grind)
    | exact resolve eq14 eq18610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18610
  have eq20990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq20776
       have i₂ := eq18477 y x
       grind)
    | exact superpose eq18477 eq20776
    | (have j1 := eq18477 y x
       grind)
    | exact resolve eq20776 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477 eq20776
  have eq20999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by grind
  clear eq20990
  have eq21000 : x = (k x y) := by grind
  clear eq20999
  have eq21132 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq21000
       grind)
    | exact superpose eq21000 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq21000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21144 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13293 x y
       have i₂ := eq21000
       grind)
    | exact superpose eq21000 eq13293
    | (have j0 := eq13293 x y
       grind)
    | exact resolve eq13293 eq21000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293 eq21000
  have eq21145 : (σ y) = (σ (k y x)) := by grind
  clear eq21144
  have eq21152 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4660
       have i₂ := eq2672 y x
       grind)
    | exact superpose eq2672 eq4660
    | (have j1 := eq2672 y x
       grind)
    | (have r₁ := eq4660
       have r₂ := eq2672 y x
       grind)
    | exact resolve eq4660 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672 eq4660
  have eq21153 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq21152
  have eq22484 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 y x x
       have i₂ := eq21132
       grind)
    | exact superpose eq21132 eq8
    | exact resolve eq8 eq21132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24252 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21132
       have i₂ := eq22484 X0
       grind)
    | exact superpose eq22484 eq21132
    | exact resolve eq21132 eq22484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21132 eq22484
  have eq24398 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24252
  have eq25562 : ∀ X0 X1 : G, x = (k x (M.op y X0)) ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq236 x y X0
       have i₂ := eq24398 X1
       grind)
    | exact superpose eq24398 eq236
    | (have j1 := eq24398 X1
       grind)
    | exact resolve eq236 eq24398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq24398
  have eq27677 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8699 x X0 y
       grind)
    | exact superpose eq8699 eq14
    | (have j1 := eq8699 x X0 x
       grind)
    | exact resolve eq14 eq8699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8699
  have eq27783 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq27677 X0
       have i₂ := eq21145
       grind)
    | exact superpose eq21145 eq27677
    | (have j0 := eq27677 X0
       grind)
    | exact resolve eq27677 eq21145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21145 eq27677
  have eq37319 : ∀ X3 : G, x = (k x (M.op y X3)) ∨ x = (k x x) := by
    intro X3
    first
    | (have i₁ := eq323 x x x x
       have i₂ := eq25562 X3 (M.op (M.op (M.op x x) x) x)
       grind)
    | exact superpose eq25562 eq323
    | (have j1 := eq25562 X3 x
       grind)
    | exact resolve eq323 eq25562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq25562
  have eq52332 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27783 X0
       have i₂ := eq21153
       grind)
    | exact superpose eq21153 eq27783
    | (have j0 := eq27783 X0
       grind)
    | (have r₁ := eq27783 X0
       have r₂ := eq21153
       grind)
    | exact resolve eq27783 eq21153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21153 eq27783
  have eq52334 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq52332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52332
  have eq52523 : x = (k x (τ (σ x))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq343 x x
       have i₂ := eq52334 (M.op (σ x) x)
       grind)
    | exact superpose eq52334 eq343
    | exact resolve eq343 eq52334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq52334
  have eq52689 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq52523
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq52523
    | exact resolve eq52523 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52523
  have eq53252 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq52689
       grind)
    | exact superpose eq52689 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq52689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52689
  have eq53266 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq53252
  have eq53369 : x = (k x x) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37319 x
       have i₂ := eq53266
       grind)
    | exact superpose eq53266 eq37319
    | exact resolve eq37319 eq53266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37319 eq53266
  have eq53445 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq53369
  have eq53482 : x = (k x x) := by
    first
    | (have j1 := eq11 x x
       grind)
    | (have r₁ := eq53445
       have r₂ := eq11 x x
       grind)
    | exact resolve eq53445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53445
  have eq53626 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq454 x
       have i₂ := eq53482
       grind)
    | exact superpose eq53482 eq454
    | (have j0 := eq454 x
       grind)
    | exact resolve eq454 eq53482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq53627 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq53482
       grind)
    | exact superpose eq53482 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq53482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53482
  have eq53641 : x = (M.op x x) := by grind
  clear eq53627
  have eq53642 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq53626
  have eq54068 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 x x x x
       have i₂ := eq53641
       grind)
    | exact superpose eq53641 eq17
    | exact resolve eq17 eq53641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55411 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq53641
       have i₂ := eq54068 x X0
       grind)
    | (have i₁ := eq53641
       have i₂ := eq54068 X0 x
       grind)
    | exact superpose eq54068 eq53641
    | exact resolve eq53641 eq54068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53641 eq54068
  have eq58103 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ x) (σ x) x x
       have i₂ := eq53642
       grind)
    | exact superpose eq53642 eq17
    | exact resolve eq17 eq53642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq68849 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq58103 (σ y) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq58103 X0 (σ y)
       grind)
    | exact superpose eq58103 eq14
    | exact resolve eq14 eq58103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68850 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq53642
       have i₂ := eq58103 (σ x) X0
       grind)
    | (have i₁ := eq53642
       have i₂ := eq58103 X0 (σ x)
       grind)
    | exact superpose eq58103 eq53642
    | exact resolve eq53642 eq58103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53642 eq58103
  have eq69015 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq68849 x
       have i₂ := eq68850 x
       grind)
    | exact superpose eq68850 eq68849
    | exact resolve eq68849 eq68850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68849 eq68850
  have eq69075 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq69015
       have i₂ := eq55411 y
       grind)
    | exact superpose eq55411 eq69015
    | exact resolve eq69015 eq55411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55411 eq69015
  have eq69076 : False := by grind
  exact eq69076

/-- `Equation4404`: `x ◇ (x ◇ y) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pyx_Equation4404 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4404 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4404.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X4) X5) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 (M.op X0 x) X4 X5
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 x X4 X5
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X0 X2 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op (M.op X0 X1) x)
       have i₂ := eq8 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X3 ∨ (M.op X0 X2) = (k (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X0 X2) X3
       grind)
    | (have r₁ := eq11 (M.op X0 X2) (M.op X0 (M.op X0 X1))
       have r₂ := eq8 X0 X1 X2 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (k X0 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X2 X1
       grind)
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq23 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq23 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq266 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X5) X6) = (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq17 X0 X1 (M.op (M.op X0 X1) x) X5 X6
       have i₂ := eq24 (M.op X0 X1) X2 X3 X4 x
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq17 (M.op (M.op X0 X2) X3) x x X4 X5
       have i₂ := eq24 X0 X2 X3 (M.op (M.op (M.op (M.op X0 X2) X3) x) x) X1
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq24
  have eq577 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X1 (M.op X0 (M.op X0 X2))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1085 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1085 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1112 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1110
    | (have j0 := eq1110 X0 X1
       grind)
    | exact resolve eq1110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq3203 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 (M.op X0 (M.op X0 X1))
       have i₂ := eq577 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq577 eq1109
    | (have j0 := eq1109 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq1109 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1109
  have eq3208 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq3203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3216 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
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
  have eq3259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3216 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3216
    | (have j0 := eq3216 X0 X1
       grind)
    | exact resolve eq3216 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216
  have eq3469 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3478 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X0 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3469 X0 (M.op X0 x)
       have i₂ := eq288 X0 x X1 X2 X3 X4
       grind)
    | exact superpose eq288 eq3469
    | exact resolve eq3469 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq3469
  have eq6607 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6614 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1112 x y
       grind)
    | exact superpose eq1112 eq14
    | (have j1 := eq1112 x y
       grind)
    | exact resolve eq14 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6615 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq1112 X1 X0
       grind)
    | exact superpose eq1112 eq32
    | (have j0 := eq32 X0 X1
       have j1 := eq1112 X0 X1
       grind)
    | exact resolve eq32 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1112
  have eq6674 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6615 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6615
  have eq6678 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6607 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6607
    | (have j0 := eq6607 X0 X1
       grind)
    | exact resolve eq6607 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6680 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6678 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6678
    | (have j0 := eq6678 X0 X1
       grind)
    | exact resolve eq6678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6678
  have eq12196 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6680 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6680
    | exact resolve eq6680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq12622 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12196 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6614
       have i₂ := eq12196 x y
       grind)
    | exact superpose eq12196 eq6614
    | (have j1 := eq12196 x y
       grind)
    | exact resolve eq6614 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq23375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6614
       have i₂ := eq3259 y x
       grind)
    | exact superpose eq3259 eq6614
    | (have j1 := eq3259 y x
       grind)
    | (have r₁ := eq6614
       have r₂ := eq3259 y x
       grind)
    | exact resolve eq6614 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq23376 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq23375
  have eq23378 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq23373
  have eq23987 : (M.op x y) = (τ (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq23376
       grind)
    | exact superpose eq23376 eq9
    | exact resolve eq9 eq23376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23376
  have eq24086 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23987
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq23987
    | exact resolve eq23987 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23987
  have eq24751 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 y X0 x X1
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq8
    | exact resolve eq8 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24820 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12622 x y
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq12622
    | (have j0 := eq12622 x y
       grind)
    | (have r₁ := eq12622 x y
       have r₂ := eq24086
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq24086
       grind)
    | exact resolve eq12622 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24827 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq24820
  have eq25064 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3259 x y
       have i₂ := eq24827
       grind)
    | exact superpose eq24827 eq3259
    | (have j0 := eq3259 x y
       grind)
    | exact resolve eq3259 eq24827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259 eq24827
  have eq25070 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by grind
  clear eq25064
  have eq29838 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24751 x X0
       have i₂ := eq24086
       grind)
    | exact superpose eq24086 eq24751
    | exact resolve eq24751 eq24086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29862 : ∀ X0 X2 : G, (M.op x X2) = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq24751 x X0
       have i₂ := eq24751 x X2
       grind)
    | exact superpose eq24751 eq24751
    | exact resolve eq24751 eq24751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24751
  have eq30151 : ∀ X0 X2 : G, (M.op x X2) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have j0 := eq29862 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29862
  have eq30153 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29838
  have eq30912 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (M.op x X1) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 x X0 y
       have i₂ := eq30151 X2 X1
       grind)
    | exact superpose eq30151 eq23
    | (have j1 := eq30151 (M.op x X0) y
       grind)
    | exact resolve eq23 eq30151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq30979 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y x) ∨ (M.op x X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12622 y x
       have i₂ := eq30151 X0 X1
       grind)
    | exact superpose eq30151 eq12622
    | (have j0 := eq12622 y x
       have j1 := eq30151 X0 X1
       grind)
    | (have r₁ := eq12622 (M.op x X0) x
       have r₂ := eq30151 X0 (M.op x X0)
       grind)
    | (have r₁ := eq12622 (M.op x x) x
       have r₂ := eq30151 (M.op x x) x
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq30151 X0 x
       grind)
    | exact resolve eq12622 eq30151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30151
  have eq30988 : ∀ X0 X1 : G, y = (k y x) ∨ (M.op x X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have j0 := eq30979 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30979
  have eq31799 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25070
       have i₂ := eq30153 X0
       grind)
    | exact superpose eq30153 eq25070
    | exact resolve eq25070 eq30153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25070
  have eq31802 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24086
       have i₂ := eq30153 X0
       grind)
    | exact superpose eq30153 eq24086
    | exact resolve eq24086 eq30153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24086 eq30153
  have eq32050 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31802
  have eq32053 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31799
  have eq32160 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq6674 X1 X0
       grind)
    | exact superpose eq6674 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq6674 X1 X0
       grind)
    | exact resolve eq11 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq32265 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32160 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq32160
    | (have j0 := eq32160 X0 X1
       grind)
    | exact resolve eq32160 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32160
  have eq32266 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32265
  have eq32538 : ∀ X0 : G, y ≠ y ∨ y = (k y x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12622 y x
       have i₂ := eq32050 X0
       grind)
    | exact superpose eq32050 eq12622
    | (have j0 := eq12622 y x
       have j1 := eq32050 X0
       grind)
    | (have r₁ := eq12622 x x
       have r₂ := eq32050 x
       grind)
    | (have r₁ := eq12622 y x
       have r₂ := eq32050 X0
       grind)
    | exact resolve eq12622 eq32050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12622 eq32050
  have eq32546 : ∀ X0 : G, y = (k y x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq32538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32538
  have eq36822 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (k y x) := by
    intro X0 X1
    first
    | (have i₁ := eq266 x x x x x X0 X1
       have i₂ := eq32546 (M.op (M.op (M.op (M.op x x) x) x) x)
       grind)
    | exact superpose eq32546 eq266
    | exact resolve eq266 eq32546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq32546
  have eq42239 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) ∨ y = (k y x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq23378
       have i₂ := eq30988 X0 y
       grind)
    | (have i₁ := eq23378
       have i₂ := eq30988 y X0
       grind)
    | exact superpose eq30988 eq23378
    | exact resolve eq23378 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23378 eq30988
  have eq42420 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) ∨ y = (k y x) := by
    intro X0
    first
    | (have j0 := eq42239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42239
  have eq59983 : ∀ X0 : G, (τ (σ y)) = (M.op x X0) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x X0)
       have i₂ := eq42420 X0
       grind)
    | exact superpose eq42420 eq9
    | exact resolve eq9 eq42420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42420
  have eq60106 : ∀ X0 : G, y = (M.op x X0) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq59983 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59983
    | exact resolve eq59983 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59983
  have eq66746 : ∀ X1 : G, x = (M.op y X1) ∨ y = (k y x) ∨ y = (k y x) := by
    intro X1
    first
    | (have i₁ := eq36822 x X1
       have i₂ := eq60106 x
       grind)
    | exact superpose eq60106 eq36822
    | exact resolve eq36822 eq60106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36822 eq60106
  have eq67164 : ∀ X1 : G, x = (M.op y X1) ∨ y = (k y x) := by
    intro X1
    first
    | (have j0 := eq66746 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66746
  have eq67883 : y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq3478 y x x x x
       have i₂ := eq67164 (M.op (M.op (M.op (M.op y x) x) x) x)
       grind)
    | exact superpose eq67164 eq3478
    | exact resolve eq3478 eq67164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3478 eq67164
  have eq67911 : y = (k y x) := by grind
  clear eq67883
  have eq89189 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq32266 y x
       have i₂ := eq67911
       grind)
    | exact superpose eq67911 eq32266
    | (have j0 := eq32266 y x
       grind)
    | exact resolve eq32266 eq67911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32266 eq67911
  have eq89199 : (σ x) = (σ (k x y)) := by grind
  clear eq89189
  have eq91366 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq89199
       grind)
    | exact superpose eq89199 eq9
    | exact resolve eq9 eq89199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89199
  have eq91479 : x = (k x y) := by
    first
    | (have i₁ := eq91366
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq91366
    | exact resolve eq91366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91366
  have eq432765 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x X1) ∨ (M.op x X1) = (M.op x (M.op x X0)) := by
    intro X0 X1
    first
    | (have j0 := eq30912 X0 X1 (M.op x X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30912
  have eq464769 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq432765 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432765
  have eq465538 : ∀ X1 X2 : G, (M.op x y) = (M.op (M.op x X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq8 x x X1 X2
       have i₂ := eq464769 x
       grind)
    | exact superpose eq464769 eq8
    | exact resolve eq8 eq464769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3208 x x
       have i₂ := eq464769 x
       grind)
    | exact superpose eq464769 eq3208
    | exact resolve eq3208 eq464769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208 eq464769
  have eq475679 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) X0) X1) = (M.op (σ (M.op x y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ (M.op x y)) X0 X1 (σ (M.op x y)) X2
       have i₂ := eq465558
       grind)
    | exact superpose eq465558 eq19
    | exact resolve eq19 eq465558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq482667 : ∀ X0 X3 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq475679 x x X3
       have i₂ := eq475679 x x X0
       grind)
    | exact superpose eq475679 eq475679
    | exact resolve eq475679 eq475679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475679
  have eq482862 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq465558
       have i₂ := eq482667 (σ (M.op x y)) X0
       grind)
    | (have i₁ := eq465558
       have i₂ := eq482667 X0 (σ (M.op x y))
       grind)
    | exact superpose eq482667 eq465558
    | exact resolve eq465558 eq482667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465558 eq482667
  have eq482937 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq482862 X0
       have i₂ := eq32053 y
       grind)
    | exact superpose eq32053 eq482862
    | exact resolve eq482862 eq32053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483808 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq482937 (σ y)
       grind)
    | exact superpose eq482937 eq14
    | exact resolve eq14 eq482937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482937
  have eq484034 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq483808
       have i₂ := eq32053 y
       grind)
    | exact superpose eq32053 eq483808
    | (have r₁ := eq483808
       have r₂ := eq32053 y
       grind)
    | exact resolve eq483808 eq32053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32053 eq483808
  have eq484035 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq484034
  have eq484036 : y = (M.op x y) := by grind
  clear eq484035
  have eq484150 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq482862 X0
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq482862
    | exact resolve eq482862 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482862
  have eq484343 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq465538 y x
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq465538
    | exact resolve eq465538 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465538
  have eq486200 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124 (σ y) X0
       have i₂ := eq484150 (σ X0)
       grind)
    | exact superpose eq484150 eq124
    | (have j0 := eq124 (σ y) X0
       grind)
    | exact resolve eq124 eq484150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq486219 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq486200 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq486200
    | (have j0 := eq486200 X0
       grind)
    | exact resolve eq486200 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486200
  have eq511228 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq486219 x
       grind)
    | exact superpose eq486219 eq14
    | (have j1 := eq486219 x
       grind)
    | exact resolve eq14 eq486219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486219
  have eq511278 : (σ y) ≠ (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq511228
       have i₂ := eq484036
       grind)
    | exact superpose eq484036 eq511228
    | exact resolve eq511228 eq484036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484036 eq511228
  have eq511279 : y = (k x y) := by grind
  clear eq511278
  have eq511290 : x = y := by
    first
    | (have i₁ := eq511279
       have i₂ := eq91479
       grind)
    | exact superpose eq91479 eq511279
    | exact resolve eq511279 eq91479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91479 eq511279
  have eq511293 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq14
    | exact resolve eq14 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511888 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq484150 X0
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq484150
    | exact resolve eq484150 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484150
  have eq511891 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq484343 X0
       have i₂ := eq511290
       grind)
    | exact superpose eq511290 eq484343
    | exact resolve eq484343 eq511290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484343 eq511290
  have eq512055 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq511293
       have i₂ := eq511891 x
       grind)
    | exact superpose eq511891 eq511293
    | exact resolve eq511293 eq511891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511293 eq511891
  have eq512076 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq512055
       have i₂ := eq511888 (σ x)
       grind)
    | exact superpose eq511888 eq512055
    | (have r₁ := eq512055
       have r₂ := eq511888 (σ x)
       grind)
    | exact resolve eq512055 eq511888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511888 eq512055
  have eq512077 : False := by grind
  exact eq512077

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation4407 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq442 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq442 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq442 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq483 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq446 (σ X0) (σ X1)
       grind)
    | exact superpose eq446 eq13
    | exact resolve eq13 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq483
    | exact resolve eq483 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq483
  have eq1187 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq490 x y
       grind)
    | exact superpose eq490 eq14
    | (have r₁ := eq14
       have r₂ := eq490 x y
       grind)
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1210 : False := by grind
  exact eq1210

/-- `Equation4411`: `x ◇ (x ◇ y) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4411 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4411 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4411.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X2 X0) X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X2 X0)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X1 X3))) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X3) X0
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X0 X1 X2 X3
       have i₂ := eq20 X2 X0 X3 X2
       grind)
    | exact superpose eq20 eq17
    | exact resolve eq17 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq33 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq75 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq120 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X4 X5) X2) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X4 X5 X2 (M.op X0 X3)
       have i₂ := eq19 X0 X3 X2 X1
       grind)
    | (have i₁ := eq20 X4 X5 X2 (M.op X0 X3)
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq188 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq22 x x X0 X4
       have i₂ := eq22 x x X0 X1
       grind)
    | (have i₁ := eq22 X0 X1 (M.op X0 X1) x
       have i₂ := eq22 X0 X1 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X0) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X3 X4
       have i₂ := eq22 X1 X2 X0 X3
       grind)
    | (have i₁ := eq8 (M.op X0 X1) (M.op X0 X1) X2
       have i₂ := eq22 X0 X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq188 X0 X2 X1
       grind)
    | (have i₁ := eq8 X0 X2 X3
       have i₂ := eq188 X0 X1 X2
       grind)
    | exact superpose eq188 eq8
    | exact resolve eq8 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq402 X2 X3 X0 X1
       grind)
    | exact superpose eq402 eq8
    | exact resolve eq8 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X5 (M.op X5 X3)) X2) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq21 X5 X3 X2 x
       have i₂ := eq402 X2 (M.op X3 x) X0 X1
       grind)
    | exact superpose eq402 eq21
    | exact resolve eq21 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x x
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op (σ X1) (M.op (M.op X2 X3) (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X3 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq22
    | (have j1 := eq31 X1 X1
       grind)
    | exact resolve eq22 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1254 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1201 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1201 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1921 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X3 X4) X2) ∨ (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98 (M.op (M.op X3 X4) X2) X2
       have i₂ := eq222 X2 X3 X4 X0 X1
       grind)
    | exact superpose eq222 eq98
    | (have j0 := eq98 (M.op (M.op X3 X4) X2) X2
       grind)
    | (have r₁ := eq98 (M.op (M.op X3 X4) X0) X0
       have r₂ := eq222 X0 X3 X4 X3 X4
       grind)
    | exact resolve eq98 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1944 : ∀ X2 X3 X4 : G, (M.op (M.op X3 X4) X2) = (k (M.op (M.op X3 X4) X2) X2) := by
    intro X2 X3 X4
    first
    | (have j0 := eq1921 x x X2 X3 X4
       grind)
    | (have r₁ := eq1921 x x X2 X3 X4
       have r₂ := eq532 x x X2 X3 X4
       grind)
    | (have r₁ := eq1921 X3 X4 X2 x x
       have r₂ := eq532 x x X2 X3 X4
       grind)
    | exact resolve eq1921 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq2199 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1254 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1254
    | (have j0 := eq1254 (τ X0) X1
       grind)
    | exact resolve eq1254 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq2202 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2199 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2199
    | (have j0 := eq2199 X0 X1
       grind)
    | exact resolve eq2199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2205 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2202 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2202
    | (have j0 := eq2202 X0 X1
       grind)
    | exact resolve eq2202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2216 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2205 (τ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq2205
    | (have j0 := eq2205 (τ X0) X1
       grind)
    | exact resolve eq2205 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2598 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | (have j0 := eq32 X1 X1
       grind)
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2598 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2598
    | (have j0 := eq2598 X0 X1
       grind)
    | exact resolve eq2598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq7113 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1250 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1250
    | (have j0 := eq1250 (τ X0)
       grind)
    | exact resolve eq1250 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7121 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7113 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7113
    | (have j0 := eq7113 X0
       grind)
    | exact resolve eq7113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7127 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7121 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7121
    | (have j0 := eq7121 X0
       grind)
    | exact resolve eq7121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq12417 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1199
       have i₂ := eq2696 y x
       grind)
    | exact superpose eq2696 eq1199
    | (have j1 := eq2696 x (σ x)
       grind)
    | (have r₁ := eq1199
       have r₂ := eq2696 y x
       grind)
    | exact resolve eq1199 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq2696
  have eq12419 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq12417
  have eq12427 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 X0 (σ x)
       have i₂ := eq12419
       grind)
    | exact superpose eq12419 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq11 X0 (σ x)
       have r₂ := eq12419
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq12419
       grind)
    | exact resolve eq11 eq12419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12419
  have eq12486 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq12427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12679 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2216 (σ x) X0
       have i₂ := eq12486 (σ x)
       grind)
    | exact superpose eq12486 eq2216
    | (have j0 := eq2216 (σ x) X0
       grind)
    | exact resolve eq2216 eq12486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216 eq12486
  have eq12705 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq12679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12679
  have eq12715 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12705 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12705
    | exact resolve eq12705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12705
  have eq12727 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq12715 X0
       have j1 := eq11 X0 x
       grind)
    | (have r₁ := eq12715 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq12715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12715
  have eq12930 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7127 x
       have i₂ := eq12727 x
       grind)
    | exact superpose eq12727 eq7127
    | (have j0 := eq7127 x
       grind)
    | (have r₁ := eq7127 x
       have r₂ := eq12727 x
       grind)
    | exact resolve eq7127 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12931 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1250 x
       have i₂ := eq12727 x
       grind)
    | exact superpose eq12727 eq1250
    | (have j0 := eq1250 x
       grind)
    | exact resolve eq1250 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq12727
  have eq12957 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq12931
  have eq12958 : x = (M.op x x) := by grind
  clear eq12930
  have eq13582 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 X2 x x X0 X1
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq222
    | exact resolve eq222 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq13588 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1 x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq402
    | exact resolve eq402 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq13591 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2 x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq532
    | exact resolve eq532 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq13596 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1944 x x x
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq1944
    | exact resolve eq1944 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq13602 : ∀ X2 : G, (M.op x X2) = (M.op X2 (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq13582 x x X2
       have i₂ := eq13591 x x X2
       grind)
    | exact superpose eq13591 eq13582
    | exact resolve eq13582 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13582
  have eq19992 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X6 (M.op X6 X7)) (M.op (M.op X3 X5) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq539 X3 X4 (M.op (M.op X3 X5) X2) X7 X6
       have i₂ := eq120 X3 X5 X2 X4 X0 X1
       grind)
    | exact superpose eq120 eq539
    | exact resolve eq539 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq20345 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op (M.op X3 X5) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19992 X0 X1 X2 X3 X4 X5 x x
       have i₂ := eq13591 x (M.op x x) (M.op (M.op X3 X5) X2)
       grind)
    | exact superpose eq13591 eq19992
    | exact resolve eq19992 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19992
  have eq20475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x (M.op x X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20345 X0 X1 X2 X3 X4 x
       have i₂ := eq13591 X3 x X2
       grind)
    | exact superpose eq13591 eq20345
    | exact resolve eq20345 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20345
  have eq20604 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op x x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20475 X0 X1 X2 X3 X4
       have i₂ := eq13588 x X2
       grind)
    | exact superpose eq13588 eq20475
    | exact resolve eq20475 eq13588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20475
  have eq20704 : ∀ X0 X1 X2 X3 X4 : G, x = (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20604 X0 X1 X2 X3 X4
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq20604
    | exact resolve eq20604 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20604
  have eq20798 : ∀ X3 X4 : G, x = (M.op x (M.op X3 X4)) := by
    intro X3 X4
    first
    | (have i₁ := eq20704 x x x X3 X4
       have i₂ := eq13591 (M.op x x) x (M.op X3 X4)
       grind)
    | exact superpose eq13591 eq20704
    | exact resolve eq20704 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20704
  have eq22487 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) X0) = (M.op (σ x) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 (σ x) (σ x) X0 X2 X1
       have i₂ := eq12957
       grind)
    | exact superpose eq12957 eq539
    | exact resolve eq539 eq12957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq22499 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq22487 X0 x x
       have i₂ := eq13591 x (M.op x x) X0
       grind)
    | exact superpose eq13591 eq22487
    | exact resolve eq22487 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22487
  have eq27397 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22499 (σ y)
       grind)
    | exact superpose eq22499 eq14
    | exact resolve eq14 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499
  have eq41443 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op x (σ X0)) X0
       have i₂ := eq13596 (σ X0)
       grind)
    | exact superpose eq13596 eq26
    | exact resolve eq26 eq13596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13596
  have eq109856 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) (M.op (M.op X1 X2) (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq94 X0 (k X3 X0) X4
       have i₂ := eq1214 X3 X0 X1 X2
       grind)
    | exact superpose eq1214 eq94
    | (have j0 := eq94 X0 X1 X4
       have j1 := eq1214 X0 X0 X2 X3
       grind)
    | exact resolve eq94 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1214
  have eq110289 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ X0) (M.op (M.op X1 X2) (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq109856 X0 X1 X2 X3 X4
       have j1 := eq11 X4 (σ X0)
       grind)
    | (have r₁ := eq109856 X0 X1 X2 X3 X4
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq109856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109856
  have eq110399 : ∀ X0 X3 X4 : G, (M.op (σ X0) (M.op x (σ X0))) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq110289 X0 x x X3 X4
       have i₂ := eq13591 x x (σ X0)
       grind)
    | exact superpose eq13591 eq110289
    | (have j0 := eq110289 X0 x x X3 X4
       grind)
    | exact resolve eq110289 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13591 eq110289
  have eq110491 : ∀ X0 X3 X4 : G, (M.op x (σ X0)) = (σ (k (k X3 X0) X0)) ∨ (k X4 (σ X0)) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq110399 X0 X3 X4
       have i₂ := eq13602 (σ X0)
       grind)
    | exact superpose eq13602 eq110399
    | (have j0 := eq110399 X0 X3 X4
       grind)
    | exact resolve eq110399 eq13602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13602 eq110399
  have eq283717 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110491 (τ X1) (τ X0) X2
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq110491
    | (have j0 := eq110491 (τ X1) x X2
       grind)
    | exact resolve eq110491 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq110491
  have eq284171 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (k (σ (τ (k X0 X1))) X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq283717 X0 X1 X2
       have i₂ := eq16 X1 (τ (k X0 X1))
       grind)
    | exact superpose eq16 eq283717
    | (have j0 := eq283717 X0 X1 X2
       grind)
    | exact resolve eq283717 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq283717
  have eq284199 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284171 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq284171
    | (have j0 := eq284171 X0 X1 X2
       grind)
    | exact resolve eq284171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284171
  have eq284214 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284199 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq284199
    | (have j0 := eq284199 X0 X1 X2
       grind)
    | exact resolve eq284199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284199
  have eq284222 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (k X0 X1) X1) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284214 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq284214
    | (have j0 := eq284214 X0 X1 X2
       grind)
    | exact resolve eq284214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284214
  have eq415764 : ∀ X0 X1 : G, (M.op x X0) = (k (τ (M.op x (σ X0))) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284222 (τ (M.op x (σ X0))) X0 X1
       have i₂ := eq41443 X0
       grind)
    | exact superpose eq41443 eq284222
    | (have j0 := eq284222 X0 X0 X1
       grind)
    | exact resolve eq284222 eq41443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284222
  have eq415965 : ∀ X0 X1 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq415764 X0 X1
       have i₂ := eq41443 X0
       grind)
    | exact superpose eq41443 eq415764
    | (have j0 := eq415764 X0 X1
       grind)
    | exact resolve eq415764 eq41443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41443 eq415764
  have eq542452 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x (σ X0))
       have i₂ := eq415965 X0 X1
       grind)
    | exact superpose eq415965 eq10
    | (have j1 := eq415965 X0 X1
       grind)
    | exact resolve eq10 eq415965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415965
  have eq660730 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq27397
       have i₂ := eq542452 y X0
       grind)
    | exact superpose eq542452 eq27397
    | (have j1 := eq542452 y X0
       grind)
    | (have r₁ := eq27397
       have r₂ := eq542452 y x
       grind)
    | exact resolve eq27397 eq542452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27397 eq542452
  have eq660768 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq660730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660730
  have eq661114 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7127 y
       have i₂ := eq660768 y
       grind)
    | exact superpose eq660768 eq7127
    | (have j0 := eq7127 y
       grind)
    | (have r₁ := eq7127 y
       have r₂ := eq660768 y
       grind)
    | exact resolve eq7127 eq660768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127 eq660768
  have eq661400 : y = (M.op y y) := by grind
  clear eq661114
  have eq664290 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq188 y X0 y
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq188
    | exact resolve eq188 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq664417 : x = (M.op x y) := by
    first
    | (have i₁ := eq20798 y y
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq20798
    | exact resolve eq20798 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20798
  have eq664571 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq664290 X0
       have i₂ := eq661400
       grind)
    | exact superpose eq661400 eq664290
    | exact resolve eq664290 eq661400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661400 eq664290
  have eq664663 : y = (M.op x y) := by
    first
    | (have i₁ := eq664571 x
       have i₂ := eq13588 y x
       grind)
    | exact superpose eq13588 eq664571
    | exact resolve eq664571 eq13588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13588 eq664571
  have eq664729 : x = y := by
    first
    | (have i₁ := eq664663
       have i₂ := eq664417
       grind)
    | exact superpose eq664417 eq664663
    | exact resolve eq664663 eq664417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664417 eq664663
  have eq667430 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq664729
       grind)
    | exact superpose eq664729 eq14
    | exact resolve eq14 eq664729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664729
  have eq667437 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq667430
       have i₂ := eq12958
       grind)
    | exact superpose eq12958 eq667430
    | exact resolve eq667430 eq12958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12958 eq667430
  have eq667439 : False := by grind
  exact eq667439

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_pxx_pxy_Equation4417 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4417 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X2 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op (M.op X2 X1) X2) ∨ (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 (M.op (M.op X2 X1) X2)
       have i₂ := eq21 X2 X1 X0
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X1 (M.op (M.op X2 X1) X2)
       grind)
    | (have r₁ := eq11 (M.op (M.op X1 (M.op (M.op X0 X1) X0)) X1) (M.op X1 (M.op (M.op X0 X1) X0))
       have r₂ := eq21 X0 X1 (M.op X1 (M.op (M.op X0 X1) X0))
       grind)
    | (have r₁ := eq11 X1 (M.op (M.op x X1) x)
       have r₂ := eq21 x X1 x
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 (M.op (M.op X3 X1) X3) X1
       have i₂ := eq21 X3 X1 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq169 : ∀ X1 X2 : G, (M.op X1 X1) = (k X1 (M.op (M.op X2 X1) X2)) := by
    intro X1 X2
    first
    | (have j0 := eq164 x X1 X2
       grind)
    | (have r₁ := eq164 x X1 x
       have r₂ := eq23 x X1 x
       grind)
    | (have r₁ := eq164 x X1 x
       have r₂ := eq23 x X1 x
       grind)
    | exact resolve eq164 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq164
  have eq195 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X0)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X2 x X3 X4
       have i₂ := eq25 X0 X1 X2 x
       grind)
    | (have i₁ := eq25 (M.op X0 (M.op X0 X1)) X0 X2 X3
       have i₂ := eq25 X0 X1 (M.op X0 (M.op X0 X1)) X3
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq252 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq169
    | exact resolve eq169 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (σ X0)) X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (M.op (M.op X1 (σ X0)) X1)
       have i₂ := eq169 (σ X0) X1
       grind)
    | exact superpose eq169 eq32
    | exact resolve eq32 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq169
  have eq637 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq14
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq14 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq11 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq663 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq640 X0 X1
       have j1 := eq11 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq640 X0 X1
       have r₂ := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq2153 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq661 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq661
    | (have j0 := eq661 (τ X0) (τ X1)
       grind)
    | exact resolve eq661 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq2160 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2153
    | (have j0 := eq2153 X0 X1
       grind)
    | exact resolve eq2153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2162 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2160 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2160
    | (have j0 := eq2160 X0 X1
       grind)
    | exact resolve eq2160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2163 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2162 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2162
    | (have j0 := eq2162 X0 X1
       grind)
    | exact resolve eq2162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2164 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2163
    | (have j0 := eq2163 X0 X1
       grind)
    | exact resolve eq2163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2165 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq2200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2165 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2165
    | (have j0 := eq2165 X0 X1
       grind)
    | exact resolve eq2165 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2208 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2164 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq2164
    | (have j0 := eq2164 (τ X0) (τ X1)
       grind)
    | exact resolve eq2164 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq9765 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq637
       have i₂ := eq2200 x y
       grind)
    | exact superpose eq2200 eq637
    | (have j1 := eq2200 (σ x) (σ y)
       grind)
    | (have r₁ := eq637
       have r₂ := eq2200 x y
       grind)
    | exact resolve eq637 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq2200
  have eq9766 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9765
  have eq9779 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X1) (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq666
    | exact resolve eq666 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq9787 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9779 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9779
    | (have j0 := eq9779 X0 X1
       grind)
    | exact resolve eq9779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9779
  have eq9788 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9787 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9787
    | (have j0 := eq9787 X0 X1
       grind)
    | exact resolve eq9787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9787
  have eq9789 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9788 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9788
    | (have j0 := eq9788 X0 X1
       grind)
    | exact resolve eq9788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9788
  have eq9790 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9789 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9789
    | (have j0 := eq9789 X0 X1
       grind)
    | exact resolve eq9789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9789
  have eq17300 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 X2 X3 (M.op X0 (M.op X0 X3)) X0
       have i₂ := eq195 X0 X3 (M.op X0 X3) X0 X1
       grind)
    | exact superpose eq195 eq166
    | exact resolve eq166 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq195
  have eq17775 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17300 X0 X1 x x
       have i₂ := eq17300 X2 X3 x x
       grind)
    | exact superpose eq17300 eq17300
    | exact resolve eq17300 eq17300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19189 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17775 X2 X3 X4 (M.op X4 x)
       have i₂ := eq17775 X4 x X0 X1
       grind)
    | (have i₁ := eq17775 X2 X3 X4 (M.op X4 x)
       have i₂ := eq17775 X0 X1 X4 x
       grind)
    | exact superpose eq17775 eq17775
    | exact resolve eq17775 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19268 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17775 X0 X1 (σ x) (σ y)
       have i₂ := eq9766
       grind)
    | exact superpose eq9766 eq17775
    | exact resolve eq17775 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19514 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X4 X2) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq17775 X2 x X0 X1
       grind)
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq17775 X0 X1 X2 x
       grind)
    | exact superpose eq17775 eq8
    | exact resolve eq8 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20770 : ∀ X0 X1 X2 X4 X5 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op X4 X5) X4) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq19514 X2 (M.op X2 x) X5 X4
       have i₂ := eq17775 X2 x X0 X1
       grind)
    | (have i₁ := eq19514 X2 (M.op X2 x) X5 X4
       have i₂ := eq17775 X0 X1 X2 x
       grind)
    | exact superpose eq17775 eq19514
    | exact resolve eq19514 eq17775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20907 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19514 X2 X3 (M.op X4 x) X4
       have i₂ := eq19514 X4 x X1 X0
       grind)
    | exact superpose eq19514 eq19514
    | exact resolve eq19514 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21032 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X4 X2) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X2 x X4
       have i₂ := eq19514 X2 x X1 X0
       grind)
    | exact superpose eq19514 eq8
    | exact resolve eq8 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21061 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252 X2 x
       have i₂ := eq19514 X2 x X1 X0
       grind)
    | exact superpose eq19514 eq252
    | exact resolve eq252 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq21294 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq17300 X2 X3 x X5
       have i₂ := eq19514 X0 X1 X5 x
       grind)
    | exact superpose eq19514 eq17300
    | exact resolve eq17300 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300
  have eq21318 : ∀ X0 X1 X2 : G, (τ (M.op (σ X2) (σ X2))) = (k X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq254 X2 x
       have i₂ := eq19514 X0 X1 (σ X2) x
       grind)
    | exact superpose eq19514 eq254
    | exact resolve eq254 eq19514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq25560 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (k X0 (M.op (M.op X1 X2) X1)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21032 X3 X4 X0 X0
       have i₂ := eq21061 X1 X2 X0
       grind)
    | exact superpose eq21061 eq21032
    | exact resolve eq21032 eq21061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21061
  have eq41341 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 (M.op X3 X4))) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20770 X3 X4 X2 X5 (M.op x (M.op x x))
       have i₂ := eq19189 x x X0 X1 X5
       grind)
    | (have i₁ := eq20770 X0 X1 X2 X2 (M.op X2 X3)
       have i₂ := eq19189 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq19189 eq20770
    | exact resolve eq20770 eq19189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19189 eq20770
  have eq46562 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21032 X3 X4 (M.op X5 x) X5
       have i₂ := eq20907 X0 X1 X5 x X2
       grind)
    | (have i₁ := eq21032 X0 X1 X4 (M.op (M.op X0 X1) X0)
       have i₂ := eq20907 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq20907 eq21032
    | exact resolve eq21032 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63390 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21032 X3 X4 (M.op X5 x) X5
       have i₂ := eq21294 X0 X1 X5 x X2
       grind)
    | (have i₁ := eq21032 X0 X1 X5 (M.op X0 (M.op X0 X1))
       have i₂ := eq21294 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq21294 eq21032
    | exact resolve eq21032 eq21294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21294
  have eq275746 : ∀ X0 X1 X2 : G, (τ (M.op (σ (τ X0)) (σ (τ X0)))) = (τ (k X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X1 (M.op X1 X2)) X0
       have i₂ := eq21318 X1 X2 (τ X0)
       grind)
    | exact superpose eq21318 eq37
    | exact resolve eq37 eq21318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq21318
  have eq275751 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq275746 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq275746
    | exact resolve eq275746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275746
  have eq277440 : ∀ X0 X1 X2 X3 : G, (τ (M.op X3 X3)) = (τ (k X3 (M.op (M.op (M.op X0 X1) X0) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq275751 X3 x x
       have i₂ := eq20907 X0 X1 x x X2
       grind)
    | (have i₁ := eq275751 X0 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq20907 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq20907 eq275751
    | exact resolve eq275751 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20907 eq275751
  have eq664230 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9766
       have i₂ := eq19268 X0 X1
       grind)
    | exact superpose eq19268 eq9766
    | exact resolve eq9766 eq19268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766 eq19268
  have eq664240 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq664230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664230
  have eq664448 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq664240 X0 (M.op X0 x)
       have i₂ := eq664240 X0 x
       grind)
    | exact superpose eq664240 eq664240
    | exact resolve eq664240 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665356 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq277440 x x (M.op (M.op (M.op x x) x) x) X0
       have i₂ := eq664240 (M.op (M.op x x) x) x
       grind)
    | exact superpose eq664240 eq277440
    | exact resolve eq277440 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277440
  have eq665370 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X0) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq46562 x x x X0 X1 (M.op (M.op (M.op (M.op x x) x) x) x)
       have i₂ := eq664240 (M.op (M.op (M.op x x) x) x) x
       grind)
    | exact superpose eq664240 eq46562
    | exact resolve eq46562 eq664240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664240
  have eq665375 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq664448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664448
  have eq665376 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665356 X0
       have i₂ := eq20 X0 y
       grind)
    | exact superpose eq20 eq665356
    | exact resolve eq665356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq665356
  have eq668474 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665370 X0 (σ y)
       have i₂ := eq665375 X0
       grind)
    | exact superpose eq665375 eq665370
    | exact resolve eq665370 eq665375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669230 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq668474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668474
  have eq672898 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq665376 (σ y)
       have i₂ := eq669230 (σ y)
       grind)
    | exact superpose eq669230 eq665376
    | exact resolve eq665376 eq669230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665376 eq669230
  have eq672912 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) := by grind
  clear eq672898
  have eq672919 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq672912
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq672912
    | exact resolve eq672912 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672912
  have eq674084 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9790 y y
       have i₂ := eq672919
       grind)
    | exact superpose eq672919 eq9790
    | (have r₁ := eq9790 y y
       have r₂ := eq672919
       grind)
    | exact resolve eq9790 eq672919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9790 eq672919
  have eq674088 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq674084
  have eq675097 : (σ y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq665370 y y
       have i₂ := eq674088
       grind)
    | exact superpose eq674088 eq665370
    | exact resolve eq665370 eq674088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665370
  have eq675098 : (σ y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq675097
  have eq675928 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq674088
       have i₂ := eq675098
       grind)
    | exact superpose eq675098 eq674088
    | exact resolve eq674088 eq675098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674088 eq675098
  have eq676187 : y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq675928
  have eq676605 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq17775 X0 X1 x y
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq17775
    | exact resolve eq17775 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17775
  have eq676657 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq21032 X0 X1 y x
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq21032
    | exact resolve eq21032 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698743 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq676605 X0 (M.op X0 x)
       have i₂ := eq676605 X0 x
       grind)
    | exact superpose eq676605 eq676605
    | exact resolve eq676605 eq676605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699753 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X0) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq46562 x x x X0 X1 (M.op (M.op (M.op (M.op x x) x) x) x)
       have i₂ := eq676605 (M.op (M.op (M.op x x) x) x) x
       grind)
    | exact superpose eq676605 eq46562
    | exact resolve eq46562 eq676605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46562 eq676605
  have eq699757 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq698743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698743
  have eq721126 : y = (M.op y x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq699753 x y
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq699753
    | exact resolve eq699753 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699753
  have eq721982 : y = (M.op y x) ∨ y = (σ y) := by grind
  clear eq721126
  have eq723359 : y = (M.op y y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq676657 y x
       have i₂ := eq721982
       grind)
    | exact superpose eq721982 eq676657
    | exact resolve eq676657 eq721982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676657 eq721982
  have eq723365 : y = (M.op y y) ∨ y = (σ y) := by grind
  clear eq723359
  have eq724547 : y ≠ y ∨ y = (k y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq723365
       grind)
    | exact superpose eq723365 eq11
    | (have r₁ := eq11 y y
       have r₂ := eq723365
       grind)
    | exact resolve eq11 eq723365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723365
  have eq724904 : y = (k y y) ∨ y = (σ y) := by grind
  clear eq724547
  have eq725589 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq2208 y y
       have i₂ := eq724904
       grind)
    | exact superpose eq724904 eq2208
    | (have j0 := eq2208 y y
       grind)
    | exact resolve eq2208 eq724904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq724904
  have eq725596 : (τ y) = (M.op (τ y) (τ y)) ∨ y = (σ y) := by grind
  clear eq725589
  have eq742431 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq699757 X0
       have i₂ := eq676187
       grind)
    | exact superpose eq676187 eq699757
    | exact resolve eq699757 eq676187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676187 eq699757
  have eq743546 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq742431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742431
  have eq745621 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq25560 y x x X0 X1
       have i₂ := eq743546 (k y (M.op (M.op x x) x))
       grind)
    | exact superpose eq743546 eq25560
    | exact resolve eq25560 eq743546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25560 eq743546
  have eq747132 : y = (M.op (τ y) (τ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq745621 (τ y) (τ y)
       have i₂ := eq725596
       grind)
    | exact superpose eq725596 eq745621
    | exact resolve eq745621 eq725596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745621
  have eq748489 : y = (M.op (τ y) (τ y)) ∨ y = (σ y) := by grind
  clear eq747132
  have eq799861 : y = (τ y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq725596
       have i₂ := eq748489
       grind)
    | exact superpose eq748489 eq725596
    | exact resolve eq725596 eq748489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725596 eq748489
  have eq800157 : y = (τ y) ∨ y = (σ y) := by grind
  clear eq799861
  have eq801294 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq800157
       grind)
    | exact superpose eq800157 eq10
    | exact resolve eq10 eq800157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800157
  have eq801301 : y = (σ y) := by grind
  clear eq801294
  have eq802302 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq801301
       grind)
    | exact superpose eq801301 eq14
    | exact resolve eq14 eq801301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802306 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665375 X0
       have i₂ := eq801301
       grind)
    | exact superpose eq801301 eq665375
    | exact resolve eq665375 eq801301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665375
  have eq813904 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq802306 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802306
  have eq813905 : y = (M.op x y) := by grind
  clear eq813904
  have eq814460 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq26 x X0 y
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq26
    | exact resolve eq26 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq814847 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq19514 X0 X1 y x
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq19514
    | exact resolve eq19514 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19514
  have eq814882 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq21032 X0 X1 y x
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq21032
    | exact resolve eq21032 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21032
  have eq814997 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41341 X1 X2 X0 x y X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq41341
    | exact resolve eq41341 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41341
  have eq815027 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63390 x y X2 X0 X1 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq63390
    | exact resolve eq63390 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63390
  have eq815062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq815027 X0 X1 X2 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq815027
    | exact resolve eq815027 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815027
  have eq815072 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X2)) X3) = (M.op X0 y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq814997 X0 X1 X2 X3
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq814997
    | exact resolve eq814997 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814997
  have eq815156 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq814460 x
       have i₂ := eq814847 x x
       grind)
    | exact superpose eq814847 eq814460
    | exact resolve eq814460 eq814847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814460
  have eq815162 : ∀ X2 X3 : G, (M.op y x) = (M.op (M.op y X2) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq815062 x x X2 X3
       have i₂ := eq814882 x x
       grind)
    | exact superpose eq814882 eq815062
    | exact resolve eq815062 eq814882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814882 eq815062
  have eq815170 : ∀ X0 X3 : G, (M.op X0 y) = (M.op (M.op y x) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq815072 X0 x x X3
       have i₂ := eq814847 x x
       grind)
    | exact superpose eq814847 eq815072
    | exact resolve eq815072 eq814847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814847 eq815072
  have eq815214 : y = (M.op y x) := by
    first
    | (have i₁ := eq815156
       have i₂ := eq813905
       grind)
    | exact superpose eq813905 eq815156
    | exact resolve eq815156 eq813905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813905 eq815156
  have eq815220 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq815170 X0 x
       have i₂ := eq815162 x x
       grind)
    | exact superpose eq815162 eq815170
    | exact resolve eq815170 eq815162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815162 eq815170
  have eq815243 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq815220 X0
       have i₂ := eq815214
       grind)
    | exact superpose eq815214 eq815220
    | exact resolve eq815220 eq815214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815214 eq815220
  have eq822047 : (σ y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq802302
       have i₂ := eq815243 x
       grind)
    | exact superpose eq815243 eq802302
    | exact resolve eq802302 eq815243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802302
  have eq822061 : y ≠ (σ y) := by
    first
    | (have i₁ := eq822047
       have i₂ := eq815243 (σ x)
       grind)
    | exact superpose eq815243 eq822047
    | exact resolve eq822047 eq815243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815243 eq822047
  have eq822713 : False := by grind
  exact eq822713

/-- `Equation4417`: `x ◇ (x ◇ y) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4417 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4417 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4417.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X3) = (M.op X1 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 (M.op X1 x) X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X3 X1
       have i₂ := eq8 X1 X2 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
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
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq33 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X1 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 (M.op X1 X3) X1
       have i₂ := eq8 X1 X3 X0
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 X3 (M.op X3 X1)
       have i₂ := eq19 X3 X1 X0
       grind)
    | (have i₁ := eq19 X2 X3 (M.op X3 X1)
       have i₂ := eq19 X0 X1 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X2 X3 (M.op X3 X0)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X2 X1)
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X2 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X3) = (M.op (M.op X2 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X1) X2 X3
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X2 X1) X2 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq101 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X3 (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 (M.op X0 X2) X3
       have i₂ := eq22 X0 X2 X1
       grind)
    | (have i₁ := eq19 X0 (M.op X0 X2) X3
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq19
    | exact resolve eq19 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 X0
       have i₂ := eq22 X0 X2 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X2) X3 X0
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X3 X2 (M.op X2 X1)
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq17 X3 X2 (M.op X2 X1)
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq939 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq887 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq887 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq955 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq939 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq939
    | (have j0 := eq939 (τ X0) X1
       grind)
    | exact resolve eq939 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq963 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1017 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq963 (τ X0) X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq963
    | (have j0 := eq963 (τ X0) X1
       grind)
    | exact resolve eq963 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq963
  have eq1091 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | (have j0 := eq32 X1 X1
       grind)
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1091 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1091
    | (have j0 := eq1091 X0 X1
       grind)
    | exact resolve eq1091 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq2252 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X0
       have i₂ := eq1146 X1 X0
       grind)
    | exact superpose eq1146 eq133
    | (have j0 := eq133 X0 X0
       have j1 := eq1146 X1 X0
       grind)
    | (have r₁ := eq133 X1 X1
       have r₂ := eq1146 X0 X1
       grind)
    | exact resolve eq133 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1146
  have eq2261 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq3448 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq939 X0 X1
       have i₂ := eq2261 X0 X2
       grind)
    | exact superpose eq2261 eq939
    | (have j0 := eq939 X0 X1
       have j1 := eq2261 X0 X2
       grind)
    | exact resolve eq939 eq2261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq2261
  have eq3495 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3448 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq3885 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq934 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq934
    | (have j0 := eq934 (τ X0)
       grind)
    | exact resolve eq934 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq934
  have eq3901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3885 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3885
    | (have j0 := eq3885 X0
       grind)
    | exact resolve eq3885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3908 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3901 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3901
    | (have j0 := eq3901 X0
       grind)
    | exact resolve eq3901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901
  have eq4296 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq128 x y X0
       grind)
    | exact superpose eq128 eq14
    | (have j1 := eq128 x x X0
       grind)
    | exact resolve eq14 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq4389 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq4296 X0
       have j1 := eq3495 x X0 x
       grind)
    | (have r₁ := eq4296 X0
       have r₂ := eq3495 x x y
       grind)
    | exact resolve eq4296 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495 eq4296
  have eq4420 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3908 (σ x)
       have i₂ := eq4389 (σ x)
       grind)
    | exact superpose eq4389 eq3908
    | (have j0 := eq3908 (σ x)
       grind)
    | (have r₁ := eq3908 (σ x)
       have r₂ := eq4389 (σ x)
       grind)
    | exact resolve eq3908 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4422 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1017 (σ x) X0
       have i₂ := eq4389 (σ x)
       grind)
    | exact superpose eq4389 eq1017
    | (have j0 := eq1017 (σ x) X0
       grind)
    | exact resolve eq1017 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq4389
  have eq4447 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq4422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq4449 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4420
  have eq4457 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4447 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4447
    | exact resolve eq4447 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq4610 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3908 x
       have i₂ := eq4457 x
       grind)
    | exact superpose eq4457 eq3908
    | (have j0 := eq3908 x
       grind)
    | (have r₁ := eq3908 x
       have r₂ := eq4457 x
       grind)
    | exact resolve eq3908 eq4457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908 eq4457
  have eq4636 : x = (M.op x x) := by grind
  clear eq4610
  have eq5004 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22 x X0 x
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq22
    | exact resolve eq22 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5011 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq55
    | exact resolve eq55 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq5013 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x x) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 x x X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq63
    | exact resolve eq63 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5038 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5013 X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5013
    | exact resolve eq5013 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq5039 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq5011 X0 X1
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5011
    | exact resolve eq5011 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5011
  have eq5042 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq5004 X0
       have i₂ := eq4636
       grind)
    | exact superpose eq4636 eq5004
    | exact resolve eq5004 eq4636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636 eq5004
  have eq5246 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) (M.op X4 (M.op X0 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 X0 (M.op X0 X5) X3 X4
       have i₂ := eq102 X0 X5 X1 X2
       grind)
    | exact superpose eq102 eq54
    | exact resolve eq54 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5303 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq101 X0 X4 X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))
       have i₂ := eq102 (M.op X0 X1) X5 X2 X3
       grind)
    | exact superpose eq102 eq101
    | exact resolve eq101 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5304 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 X4 X0 (M.op (M.op X0 X1) (M.op (M.op X0 X1) X5)) X1
       have i₂ := eq102 (M.op X0 X1) X5 X2 X3
       grind)
    | exact superpose eq102 eq51
    | exact resolve eq51 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq5311 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X0)) = (M.op (M.op (M.op X4 X0) X4) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq20 X4 X0 X2 (M.op (M.op X0 X2) x)
       have i₂ := eq102 X0 X1 X2 x
       grind)
    | exact superpose eq102 eq20
    | exact resolve eq20 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102
  have eq5410 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 (M.op X0 X1)) X0)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5311 X0 X1 X2 x
       have i₂ := eq5039 x X0
       grind)
    | exact superpose eq5039 eq5311
    | exact resolve eq5311 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5311
  have eq5413 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5304 X0 X1 X2 X3 X4 x
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5304
    | exact resolve eq5304 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5414 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) X3)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5303 X0 X1 X2 X3 X4 x
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5303
    | exact resolve eq5303 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5449 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq5246 X0 X1 x X3 X4 X5
       have i₂ := eq5038 (M.op X0 X1) x
       grind)
    | exact superpose eq5038 eq5246
    | exact resolve eq5246 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5556 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op x (M.op (M.op X0 X1) x))) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5410 X0 X1 X2
       have i₂ := eq5039 X0 (M.op X0 X1)
       grind)
    | exact superpose eq5039 eq5410
    | exact resolve eq5410 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410
  have eq5559 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X0) X4) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5413 X0 X1 X2 x X4
       have i₂ := eq5038 (M.op (M.op X0 X1) X2) x
       grind)
    | exact superpose eq5038 eq5413
    | exact resolve eq5413 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413
  have eq5560 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X0 X4)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5414 X0 X1 X2 x X4
       have i₂ := eq5038 (M.op (M.op X0 X1) X2) x
       grind)
    | exact superpose eq5038 eq5414
    | exact resolve eq5414 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038 eq5414
  have eq5584 : ∀ X0 X1 X4 X5 : G, (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op X4 (M.op X0 X5))) = (M.op x (M.op X4 x)) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq5449 X0 X1 x X4 X5
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq5449
    | exact resolve eq5449 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5667 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 x)) X0) = (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5559 X0 X1 X2 x
       have i₂ := eq5039 x X0
       grind)
    | exact superpose eq5039 eq5559
    | exact resolve eq5559 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5559
  have eq5668 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x (M.op (M.op (M.op X0 X1) X2) x)) (M.op x (M.op (M.op X0 X1) x))) = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq5560 X0 X1 X2 X4
       have i₂ := eq5039 X0 (M.op X0 X4)
       grind)
    | exact superpose eq5039 eq5560
    | exact resolve eq5560 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5560
  have eq5723 : ∀ X0 : G, (M.op x (M.op x x)) = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq5667 X0 x x
       have i₂ := eq5584 (M.op X0 x) x x x
       grind)
    | exact superpose eq5584 eq5667
    | exact resolve eq5667 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5724 : ∀ X0 X4 : G, (M.op x (M.op x x)) = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X4
    first
    | (have i₁ := eq5668 X0 x x X4
       have i₂ := eq5584 (M.op X0 x) x x x
       grind)
    | exact superpose eq5584 eq5668
    | exact resolve eq5668 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5760 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 x)) X0) := by
    intro X0
    first
    | (have i₁ := eq5723 X0
       have i₂ := eq5042 x
       grind)
    | exact superpose eq5042 eq5723
    | exact resolve eq5723 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq5761 : ∀ X0 X4 : G, x = (M.op x (M.op (M.op X0 X4) x)) := by
    intro X0 X4
    first
    | (have i₁ := eq5724 X0 X4
       have i₂ := eq5042 x
       grind)
    | exact superpose eq5042 eq5724
    | exact resolve eq5724 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5939 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq151 X2 (M.op (M.op X3 X1) X3) X1 X4
       have i₂ := eq17 X3 X1 X0
       grind)
    | exact superpose eq17 eq151
    | exact resolve eq151 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq5949 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op (M.op X3 X4) X3) (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq151 X3 X4 (M.op X4 X2) X5
       have i₂ := eq54 X0 X1 X4 X2
       grind)
    | (have i₁ := eq151 X0 (M.op X3 X1) (M.op (M.op X0 X1) X0) X3
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq151
    | exact resolve eq151 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq5968 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X4 X3) X4) (M.op (M.op X5 (M.op (M.op X4 X3) X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq151 X2 (M.op X0 X3) (M.op (M.op X4 X3) X4) X5
       have i₂ := eq63 X4 X3 X0 X1
       grind)
    | (have i₁ := eq151 X0 (M.op X2 X3) X2 X3
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq151
    | exact resolve eq151 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq6062 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq151 X3 X4 X2 (M.op (M.op X1 X2) X1)
       have i₂ := eq64 X1 X2 (M.op (M.op X1 X2) X1) X0
       grind)
    | exact superpose eq64 eq151
    | exact resolve eq151 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq151
  have eq6320 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 (M.op x (M.op (M.op (M.op (M.op X1 X2) X1) X2) x))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq6062 x X1 X2 X3 X4
       have i₂ := eq5039 x (M.op (M.op (M.op X1 X2) X1) X2)
       grind)
    | exact superpose eq5039 eq6062
    | exact resolve eq6062 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6062
  have eq6368 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X4 X3) X4) (M.op x (M.op (M.op (M.op X4 X3) X4) x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5968 X0 X1 X2 X3 X4 x
       have i₂ := eq5039 x (M.op (M.op X4 X3) X4)
       grind)
    | exact superpose eq5039 eq5968
    | exact resolve eq5968 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq6387 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op (M.op X3 X4) X3) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq5949 x X1 X2 X3 X4 X5
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq5949
    | exact resolve eq5949 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq6393 : ∀ X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op (M.op X2 (M.op (M.op X3 X1) X3)) X2) (M.op x (M.op X1 x))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq5939 x X1 X2 X3 X4
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq5939
    | exact resolve eq5939 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq6534 : ∀ X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X3) (M.op X2 X4)) = (M.op X2 x) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq6320 x X2 X3 X4
       have i₂ := eq5761 (M.op (M.op x X2) x) X2
       grind)
    | exact superpose eq5761 eq6320
    | exact resolve eq6320 eq5761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq6574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) = (M.op (M.op x (M.op (M.op X4 X3) x)) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6368 X0 X1 X2 X3 X4
       have i₂ := eq5556 (M.op X4 X3) X4 X4
       grind)
    | exact superpose eq5556 eq6368
    | exact resolve eq6368 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq6593 : ∀ X1 X2 X4 X5 : G, (M.op (M.op X4 X2) (M.op (M.op X5 (M.op X4 X2)) X5)) = (M.op (M.op x (M.op X4 x)) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X4 X5
    first
    | (have i₁ := eq6387 X1 X2 x X4 X5
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq6387
    | exact resolve eq6387 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6599 : ∀ X1 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op (M.op x (M.op (M.op (M.op X3 X1) X3) x)) (M.op x (M.op X1 x))) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq6393 X1 x X3 X4
       have i₂ := eq5039 x (M.op (M.op X3 X1) X3)
       grind)
    | exact superpose eq5039 eq6393
    | exact resolve eq6393 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq6714 : ∀ X2 X4 : G, (M.op X2 x) = (M.op (M.op x (M.op X4 x)) (M.op X2 X4)) := by
    intro X2 X4
    first
    | (have i₁ := eq6534 X2 x X4
       have i₂ := eq5039 x X4
       grind)
    | exact superpose eq5039 eq6534
    | exact resolve eq6534 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6741 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op X2 (M.op X0 X3)) X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6574 X0 X1 X2 X3 x
       have i₂ := eq5760 (M.op x X3)
       grind)
    | exact superpose eq5760 eq6574
    | exact resolve eq6574 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760 eq6574
  have eq6760 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X2) (M.op x (M.op (M.op X4 X2) x))) = (M.op (M.op x (M.op X4 x)) (M.op (M.op x (M.op X1 x)) (M.op X2 X1))) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq6593 X1 X2 X4 x
       have i₂ := eq5039 x (M.op X4 X2)
       grind)
    | exact superpose eq5039 eq6593
    | exact resolve eq6593 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6593
  have eq6766 : ∀ X1 X4 : G, (M.op X1 (M.op (M.op X4 X1) X4)) = (M.op x (M.op x (M.op X1 x))) := by
    intro X1 X4
    first
    | (have i₁ := eq6599 X1 x X4
       have i₂ := eq5761 (M.op x X1) x
       grind)
    | exact superpose eq5761 eq6599
    | exact resolve eq6599 eq5761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761 eq6599
  have eq6882 : ∀ X0 X1 X3 : G, x = (M.op (M.op x (M.op (M.op X0 X3) x)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6741 X0 X1 x X3
       have i₂ := eq5039 x (M.op X0 X3)
       grind)
    | exact superpose eq5039 eq6741
    | exact resolve eq6741 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6741
  have eq6898 : ∀ X2 X4 : G, (M.op (M.op X4 X2) (M.op x (M.op (M.op X4 X2) x))) = (M.op (M.op x (M.op X4 x)) (M.op X2 x)) := by
    intro X2 X4
    first
    | (have i₁ := eq6760 x X2 X4
       have i₂ := eq6714 X2 x
       grind)
    | exact superpose eq6714 eq6760
    | exact resolve eq6760 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714 eq6760
  have eq6904 : ∀ X1 X4 : G, x = (M.op X1 (M.op (M.op X4 X1) X4)) := by
    intro X1 X4
    first
    | (have i₁ := eq6766 X1 X4
       have i₂ := eq5042 (M.op X1 x)
       grind)
    | exact superpose eq5042 eq6766
    | exact resolve eq6766 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042 eq6766
  have eq6982 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq6882 X0 x x
       have i₂ := eq5584 X0 x X0 x
       grind)
    | exact superpose eq5584 eq6882
    | exact resolve eq6882 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584 eq6882
  have eq6996 : ∀ X2 X4 : G, (M.op (M.op x (M.op X4 x)) X4) = (M.op (M.op x (M.op X4 x)) (M.op X2 x)) := by
    intro X2 X4
    first
    | (have i₁ := eq6898 X2 X4
       have i₂ := eq5556 X4 X2 X2
       grind)
    | exact superpose eq5556 eq6898
    | exact resolve eq6898 eq5556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq6898
  have eq6998 : ∀ X1 : G, x = (M.op X1 (M.op x (M.op X1 x))) := by
    intro X1
    first
    | (have i₁ := eq6904 X1 x
       have i₂ := eq5039 x X1
       grind)
    | exact superpose eq5039 eq6904
    | exact resolve eq6904 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039 eq6904
  have eq7038 : ∀ X2 X4 : G, (M.op x (M.op X2 x)) = (M.op x X4) := by
    intro X2 X4
    first
    | (have i₁ := eq6996 X2 x
       have i₂ := eq6982 x
       grind)
    | exact superpose eq6982 eq6996
    | exact resolve eq6996 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7040 : ∀ X1 : G, x = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq6998 X1
       have i₂ := eq6982 X1
       grind)
    | exact superpose eq6982 eq6998
    | exact resolve eq6998 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6998
  have eq7061 : ∀ X4 : G, x = (M.op x X4) := by
    intro X4
    first
    | (have i₁ := eq7038 x X4
       have i₂ := eq6982 x
       grind)
    | exact superpose eq6982 eq7038
    | exact resolve eq7038 eq6982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982 eq7038
  have eq7132 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x
       have i₂ := eq7040 (M.op x X1)
       grind)
    | exact superpose eq7040 eq19
    | exact resolve eq19 eq7040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7040
  have eq29968 : x = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7132 (σ x) (σ x)
       have i₂ := eq4449
       grind)
    | exact superpose eq4449 eq7132
    | exact resolve eq7132 eq4449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7132
  have eq30917 : x = (σ x) := by
    first
    | (have i₁ := eq4449
       have i₂ := eq29968
       grind)
    | exact superpose eq29968 eq4449
    | exact resolve eq4449 eq29968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449 eq29968
  have eq32703 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30917
       grind)
    | exact superpose eq30917 eq14
    | exact resolve eq14 eq30917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32747 : x ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq32703
       have i₂ := eq7061 (σ y)
       grind)
    | exact superpose eq7061 eq32703
    | exact resolve eq32703 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32703
  have eq32758 : x ≠ (σ x) := by
    first
    | (have i₁ := eq32747
       have i₂ := eq7061 y
       grind)
    | exact superpose eq7061 eq32747
    | exact resolve eq32747 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7061 eq32747
  have eq32761 : False := by grind
  exact eq32761
