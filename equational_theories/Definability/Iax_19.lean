import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3714 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3714 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
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
  have eq28 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq98 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq32 X1 (τ X0)
       grind)
    | exact superpose eq32 eq16
    | (have j1 := eq32 X1 X1
       grind)
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq121 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq106
    | exact resolve eq106 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq131 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X0 X0)
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (M.op X1 X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq30 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X1)
       grind)
    | exact superpose eq12 eq30
    | (have j0 := eq30 X2 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq30 X1 X0 X0
       grind)
    | exact superpose eq30 eq18
    | (have j1 := eq30 X1 X0 x
       grind)
    | exact resolve eq18 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30
  have eq157 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq147
    | (have j0 := eq147 X0 X1
       grind)
    | exact resolve eq147 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq188 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0
       have i₂ := eq32 (σ X0) X1
       grind)
    | exact superpose eq32 eq121
    | (have j1 := eq32 (σ X0) X1
       grind)
    | exact resolve eq121 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq292 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (M.op (σ X0) (σ X0)) (σ X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq13
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq13 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq631 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq204 X0 X1
       grind)
    | exact resolve eq12 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq650 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq966 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1032 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq966 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq966
    | (have j0 := eq966 X0 X1
       grind)
    | exact resolve eq966 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1200 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq10
    | (have j1 := eq37 X0 X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1329 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1329 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1329
    | (have j0 := eq1329 X0 X1
       grind)
    | exact resolve eq1329 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq2009 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq14
    | (have j1 := eq60 x y
       grind)
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2011 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq60 X0 X0
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2457 : ∀ X0 X1 X2 : G, X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1289 X1 X0
       have i₂ := eq650 X0 X2
       grind)
    | exact superpose eq650 eq1289
    | (have j0 := eq1289 X1 X0
       have j1 := eq650 X0 X2
       grind)
    | exact resolve eq1289 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq2522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1379 y x
       grind)
    | exact superpose eq1379 eq305
    | (have j1 := eq1379 y x
       grind)
    | (have r₁ := eq305
       have r₂ := eq1379 y x
       grind)
    | exact resolve eq305 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1289 y x
       grind)
    | exact superpose eq1289 eq305
    | (have j1 := eq1289 (σ y) (σ x)
       grind)
    | (have r₁ := eq305
       have r₂ := eq1289 y x
       grind)
    | exact resolve eq305 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq2524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq1032 x y
       grind)
    | exact superpose eq1032 eq305
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq305
       have r₂ := eq1032 x y
       grind)
    | exact resolve eq305 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq2525 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2524
  have eq2526 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2523
  have eq2527 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2522
  have eq2548 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq2525
       grind)
    | exact superpose eq2525 eq20
    | exact resolve eq20 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq2561 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2548
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq2548
    | exact resolve eq2548 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq3152 : ∀ X0 X1 X2 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq32 (σ X0) X2
       grind)
    | exact superpose eq32 eq317
    | (have j0 := eq317 X0 X1
       have j1 := eq32 (σ X0) X2
       grind)
    | exact resolve eq317 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3168 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq317
    | exact resolve eq317 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3238 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3168 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq3168
    | (have j0 := eq3168 X0 X1
       grind)
    | exact resolve eq3168 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3244 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3152 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3152
    | (have j0 := eq3152 X0 X1 X2
       grind)
    | exact resolve eq3152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3271 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq2561
       grind)
    | exact superpose eq2561 eq9
    | exact resolve eq9 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq3318 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3271
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3271
    | exact resolve eq3271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3319 : y = (k y y) := by
    first
    | (have j1 := eq67 y y
       grind)
    | (have r₁ := eq3318
       have r₂ := eq67 y y
       grind)
    | exact resolve eq3318 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3472 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq338 y
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq338
    | (have j0 := eq338 y
       grind)
    | exact resolve eq338 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq3479 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq32 y y
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq32
    | (have j0 := eq32 y x
       grind)
    | exact resolve eq32 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3319
  have eq3486 : y = (M.op y y) := by grind
  clear eq3479
  have eq3489 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3472
  have eq3571 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 X0
       have i₂ := eq143 X0 X2 X1
       grind)
    | exact superpose eq143 eq67
    | (have j0 := eq67 X1 X0
       have j1 := eq143 X1 X2 X1
       grind)
    | (have r₁ := eq67 X0 X0
       have r₂ := eq143 X0 X1 X0
       grind)
    | exact resolve eq67 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq143
  have eq3728 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3571 X0 X1 X2
       have j1 := eq28 (k X1 X0) X2 X1
       grind)
    | (have r₁ := eq3571 X0 X2 X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | (have r₁ := eq3571 X2 X0 X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | (have r₁ := eq3571 (M.op X1 X2) (k X1 X2) X2
       have r₂ := eq28 X0 X1 X2
       grind)
    | exact resolve eq3571 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3571
  have eq3736 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131 X0 y
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq131
    | exact resolve eq131 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq3936 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq157 (σ y) x
       have i₂ := eq3489
       grind)
    | exact superpose eq3489 eq157
    | (have j0 := eq157 (σ y) X0
       grind)
    | exact resolve eq157 eq3489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq3489
  have eq7017 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq318 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq318
    | exact resolve eq318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq7199 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X2)) = (k (M.op X0 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7017 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq7017
    | (have j0 := eq7017 X0 X1 X2
       grind)
    | exact resolve eq7017 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7519 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319 (τ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq319
    | exact resolve eq319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq7702 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X2 X1)) = (k (σ X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7519 X0 X1 X2
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq7519
    | (have j0 := eq7519 X0 X1 X2
       grind)
    | exact resolve eq7519 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7519
  have eq7763 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq317 x x
       have i₂ := eq2526
       grind)
    | exact superpose eq2526 eq317
    | exact resolve eq317 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq7799 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7763
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7763
    | exact resolve eq7763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7763
  have eq9525 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq121 x
       have i₂ := eq2527
       grind)
    | exact superpose eq2527 eq121
    | exact resolve eq121 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq9584 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9525
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9525
    | exact resolve eq9525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9585 : x = (k x y) := by grind
  clear eq9584
  have eq33164 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq3238 X0 X1
       grind)
    | exact superpose eq3238 eq25
    | (have j1 := eq3238 X0 X1
       grind)
    | exact resolve eq25 eq3238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq34246 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X0))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1
       have i₂ := eq54 (σ X1) X0
       grind)
    | exact superpose eq54 eq121
    | (have j1 := eq54 (σ X1) X0
       grind)
    | exact resolve eq121 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq121
  have eq34562 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ (M.op (σ X1) (σ X0))) = (k (τ (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34246 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34246
    | (have j0 := eq34246 X0 X1
       grind)
    | exact resolve eq34246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34246
  have eq34683 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34562 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq34562
    | (have j0 := eq34562 X0 X1
       grind)
    | exact resolve eq34562 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34562
  have eq36719 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1253 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq36721 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq36719 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36719
    | (have j0 := eq36719 X0
       grind)
    | exact resolve eq36719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36719
  have eq37122 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq36721 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq36721
    | (have j0 := eq36721 (M.op X0 X0)
       grind)
    | (have r₁ := eq36721 (M.op X0 X0)
       have r₂ := eq20 X0
       grind)
    | exact resolve eq36721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36721
  have eq37151 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq37122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37122
  have eq58053 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34683 x x
       have i₂ := eq2526
       grind)
    | exact superpose eq2526 eq34683
    | (have j0 := eq34683 x x
       grind)
    | exact resolve eq34683 eq2526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34683
  have eq58131 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58053
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq58053
    | exact resolve eq58053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58053
  have eq61383 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq7799
       grind)
    | exact superpose eq7799 eq9
    | exact resolve eq9 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7799
  have eq61396 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq61383
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq61383
    | exact resolve eq61383 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61383
  have eq61468 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46 x x
       have i₂ := eq61396
       grind)
    | exact superpose eq61396 eq46
    | exact resolve eq46 eq61396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61396
  have eq61493 : y = (M.op x x) ∨ x = y := by grind
  clear eq61468
  have eq62656 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) (σ (τ X1))) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7199 X2 (τ X0) (τ X1)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq7199
    | (have j0 := eq7199 X2 (τ X0) X2
       grind)
    | exact resolve eq7199 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq62690 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62656 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq62656
    | (have j0 := eq62656 X0 X1 X2
       grind)
    | exact resolve eq62656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62656
  have eq62696 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X2 X2) X1) ∨ (k X2 (σ (τ X0))) = (M.op X2 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62690 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq62690
    | (have j0 := eq62690 X0 X1 X2
       grind)
    | exact resolve eq62690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62690
  have eq62697 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (k X0 X1) = (k (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62696 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62696
    | (have j0 := eq62696 X0 X1 X2
       grind)
    | exact resolve eq62696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62696
  have eq62770 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7702 X2 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq7702
    | (have j0 := eq7702 X2 (τ X1) X2
       grind)
    | exact resolve eq7702 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7702
  have eq62812 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62770 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62770
    | (have j0 := eq62770 X0 X1 X2
       grind)
    | exact resolve eq62770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62770
  have eq62817 : ∀ X0 X1 X2 : G, (k X0 X1) = (k X0 (M.op X2 X2)) ∨ (k X2 (σ (τ X1))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62812 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq62812
    | (have j0 := eq62812 X0 X1 X2
       grind)
    | exact resolve eq62812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62812
  have eq62818 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62817 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62817
    | (have j0 := eq62817 X0 X1 X2
       grind)
    | exact resolve eq62817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62817
  have eq64493 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq58131
  have eq64511 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq64493
       have r₂ := eq61493
       grind)
    | exact resolve eq64493 eq61493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64493
  have eq67483 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2011 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq67484 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq67483 X0 X1
       have j1 := eq292 X1 X0
       grind)
    | (have r₁ := eq67483 (k X1 X1) X0
       have r₂ := eq292 X0 X1
       grind)
    | (have r₁ := eq67483 X0 (σ (k X1 X1))
       have r₂ := eq292 (σ X0) X1
       grind)
    | (have r₁ := eq67483 X1 X0
       have r₂ := eq292 X0 X1
       grind)
    | exact resolve eq67483 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq67483
  have eq67679 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq67484 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq67484 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq67484 eq16
    | (have j1 := eq67484 (τ X1) X0
       grind)
    | exact resolve eq16 eq67484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67680 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq67484 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq67484 X0 (σ X0)
       grind)
    | exact superpose eq67484 eq9
    | (have j1 := eq67484 X1 X0
       grind)
    | exact resolve eq9 eq67484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67484
  have eq67699 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67679 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq67679
    | (have j0 := eq67679 X0 X1
       grind)
    | exact resolve eq67679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67679
  have eq67706 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67699 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67699
    | (have j0 := eq67699 X0 X1
       grind)
    | exact resolve eq67699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67699
  have eq67717 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq3244 x y X0
       grind)
    | exact superpose eq3244 eq14
    | (have j1 := eq3244 x y X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq3244 (σ (M.op x y)) (M.op (σ x) (σ y)) x
       grind)
    | (have r₁ := eq14
       have r₂ := eq3244 (M.op (σ x) (σ y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq14 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq67720 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq67717 X0
       have j1 := eq2457 x y X0
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 (σ (M.op x y)) (σ (k x y)) x
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 (σ (k x y)) (σ (M.op x y)) x
       grind)
    | (have r₁ := eq67717 X0
       have r₂ := eq2457 x y x
       grind)
    | exact resolve eq67717 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq67717
  have eq67738 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25 X0 x
       have i₂ := eq67720 X0
       grind)
    | exact superpose eq67720 eq25
    | exact resolve eq25 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq67759 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq67720 (σ X0)
       grind)
    | exact superpose eq67720 eq13
    | exact resolve eq13 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67762 : ∀ X0 : G, (k X0 (τ (σ x))) = (τ (M.op (σ X0) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq42 X0 (σ x)
       have i₂ := eq67720 (σ X0)
       grind)
    | exact superpose eq67720 eq42
    | exact resolve eq42 eq67720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67720
  have eq67775 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq67762 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq67762
    | exact resolve eq67762 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67762
  have eq67951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq67706 y x
       grind)
    | exact superpose eq67706 eq305
    | (have j1 := eq67706 y x
       grind)
    | exact resolve eq305 eq67706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq67952 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2009
       have i₂ := eq67706 y x
       grind)
    | exact superpose eq67706 eq2009
    | (have j1 := eq67706 y x
       grind)
    | exact resolve eq2009 eq67706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq67706
  have eq68133 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq67952
  have eq68134 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq67951
  have eq68432 : (M.op (σ x) (σ x)) = (σ (M.op (k (τ (σ x)) x) (k (τ (σ x)) x))) ∨ x = y := by
    first
    | (have i₁ := eq37151 (σ x)
       have i₂ := eq67738 (σ x)
       grind)
    | exact superpose eq67738 eq37151
    | exact resolve eq37151 eq67738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67738
  have eq68459 : (M.op (σ x) (σ x)) = (σ (M.op (k x x) (k x x))) ∨ x = y := by
    first
    | (have i₁ := eq68432
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq68432
    | exact resolve eq68432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68432
  have eq69035 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq67775 x
       have i₂ := eq68134
       grind)
    | exact superpose eq68134 eq67775
    | exact resolve eq67775 eq68134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67775 eq68134
  have eq69127 : y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq69035
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq69035
    | exact resolve eq69035 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69035
  have eq69128 : y = (k x x) ∨ x = y := by grind
  clear eq69127
  have eq69278 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1379 x x
       have i₂ := eq69128
       grind)
    | exact superpose eq69128 eq1379
    | exact resolve eq1379 eq69128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq69287 : ∀ X0 : G, x = y ∨ (M.op X0 x) = (k X0 x) ∨ (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3728 x x X0
       have i₂ := eq69128
       grind)
    | exact superpose eq69128 eq3728
    | (have j0 := eq3728 x x X0
       grind)
    | exact resolve eq3728 eq69128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq69128
  have eq69306 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq69287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69287
  have eq69307 : (σ y) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq69278
  have eq69819 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq69306 (τ X0)
       grind)
    | exact superpose eq69306 eq16
    | exact resolve eq16 eq69306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq69306
  have eq69972 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq67759 (M.op x x)
       have i₂ := eq69307
       grind)
    | exact superpose eq69307 eq67759
    | exact resolve eq67759 eq69307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67759 eq69307
  have eq69975 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) x)) ∨ x = y := by grind
  clear eq69972
  have eq71320 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69819 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69819
    | exact resolve eq69819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69819
  have eq71366 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq71320 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq71320
    | exact resolve eq71320 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71320
  have eq75451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq67680 (σ X1) X0
       grind)
    | exact superpose eq67680 eq13
    | (have j1 := eq67680 (σ X1) X0
       grind)
    | exact resolve eq13 eq67680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67680
  have eq75458 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75451 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq75451
    | (have j0 := eq75451 X0 X1
       grind)
    | exact resolve eq75451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75451
  have eq76625 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75458 x y
       grind)
    | exact superpose eq75458 eq14
    | (have j1 := eq75458 x y
       grind)
    | exact resolve eq14 eq75458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75458
  have eq76658 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq76625
       have i₂ := eq9585
       grind)
    | exact superpose eq9585 eq76625
    | exact resolve eq76625 eq9585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585 eq76625
  have eq76671 : y = (k x x) := by
    first
    | (have r₁ := eq76658
       have r₂ := eq68133
       grind)
    | exact resolve eq76658 eq68133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68133 eq76658
  have eq82017 : (M.op (σ y) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq71366 (M.op x x)
       have i₂ := eq69975
       grind)
    | exact superpose eq69975 eq71366
    | exact resolve eq71366 eq69975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69975 eq71366
  have eq82025 : (M.op (σ y) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = y := by grind
  clear eq82017
  have eq83572 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq82025
       have i₂ := eq61493
       grind)
    | exact superpose eq61493 eq82025
    | exact resolve eq82025 eq61493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61493 eq82025
  have eq83590 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y := by grind
  clear eq83572
  have eq85548 : ∀ X0 : G, (k (τ (σ X0)) X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq33164 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33164
  have eq85549 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq85548 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq85548
    | (have j0 := eq85548 X0
       grind)
    | exact resolve eq85548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85548
  have eq85614 : x ≠ x ∨ x = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85549 x
       have i₂ := eq64511
       grind)
    | exact superpose eq64511 eq85549
    | (have j0 := eq85549 x
       grind)
    | (have r₁ := eq85549 x
       have r₂ := eq64511
       grind)
    | exact resolve eq85549 eq64511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64511 eq85549
  have eq85646 : x = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq85614
  have eq85885 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37151 (σ x)
       have i₂ := eq85646
       grind)
    | exact superpose eq85646 eq37151
    | exact resolve eq37151 eq85646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37151 eq85646
  have eq86961 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2526
       have i₂ := eq85885
       grind)
    | exact superpose eq85885 eq2526
    | exact resolve eq2526 eq85885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526 eq85885
  have eq87001 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq86961
  have eq87030 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq87001
       grind)
    | exact superpose eq87001 eq9
    | exact resolve eq9 eq87001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87001
  have eq87052 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87030
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq87030
    | exact resolve eq87030 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87030
  have eq87053 : y = (M.op x x) := by grind
  clear eq87052
  have eq87169 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8 x X0
       have i₂ := eq87053
       grind)
    | exact superpose eq87053 eq8
    | exact resolve eq8 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87053
  have eq90662 : ∀ X0 X1 : G, (k X0 X1) = (k y X1) ∨ (M.op y X0) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62697 X0 X1 y
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq62697
    | (have j0 := eq62697 X0 X1 y
       grind)
    | exact resolve eq62697 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62697
  have eq91342 : ∀ X0 : G, (k X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq90662 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90662
  have eq91709 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91342 X0
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq91342
    | (have j0 := eq91342 X0
       have j1 := eq46 X0 y
       grind)
    | (have r₁ := eq91342 y
       have r₂ := eq46 y y
       grind)
    | exact resolve eq91342 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq91342
  have eq91750 : ∀ X0 X1 : G, (M.op y X0) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91709 X0 y
       have j1 := eq3736 X0
       grind)
    | (have r₁ := eq91709 X0 X1
       have r₂ := eq3736 X0
       grind)
    | exact resolve eq91709 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736 eq91709
  have eq92838 : ∀ X0 : G, (M.op y X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq91750 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91750
  have eq92839 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq92838 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92838
  have eq93075 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq92839 (τ X0)
       grind)
    | exact superpose eq92839 eq17
    | exact resolve eq17 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq96218 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62818 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62818
  have eq96219 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq96218
  have eq103523 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq42 y X0
       have i₂ := eq3936 X0
       grind)
    | exact superpose eq3936 eq42
    | (have j1 := eq3936 X0
       grind)
    | exact resolve eq42 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3936
  have eq103528 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq103523 X0
       have i₂ := eq92839 (τ X0)
       grind)
    | exact superpose eq92839 eq103523
    | (have j0 := eq103523 X0
       grind)
    | exact resolve eq103523 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103523
  have eq121963 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq68459
       have i₂ := eq76671
       grind)
    | exact superpose eq76671 eq68459
    | exact resolve eq68459 eq76671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68459 eq76671
  have eq121976 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq121963
       have i₂ := eq3486
       grind)
    | exact superpose eq3486 eq121963
    | exact resolve eq121963 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486 eq121963
  have eq122415 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) X0
       have i₂ := eq121976
       grind)
    | exact superpose eq121976 eq8
    | exact resolve eq8 eq121976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121976
  have eq123373 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq122415 (σ y)
       have i₂ := eq83590
       grind)
    | exact superpose eq83590 eq122415
    | exact resolve eq122415 eq83590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83590 eq122415
  have eq123376 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ x = y := by grind
  clear eq123373
  have eq131191 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ y) X0)
       have i₂ := eq103528 X0
       grind)
    | exact superpose eq103528 eq10
    | (have j1 := eq103528 X0
       grind)
    | exact resolve eq10 eq103528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103528
  have eq131192 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq131191 X0
       have i₂ := eq93075 X0
       grind)
    | exact superpose eq93075 eq131191
    | (have j0 := eq131191 X0
       grind)
    | exact resolve eq131191 eq93075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93075 eq131191
  have eq131193 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq131192 X0
       have j1 := eq96219 (σ y) X0
       grind)
    | (have r₁ := eq131192 x
       have r₂ := eq96219 (σ y) x
       grind)
    | exact resolve eq131192 eq96219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96219 eq131192
  have eq131302 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq131193 (σ X0)
       grind)
    | exact superpose eq131193 eq13
    | exact resolve eq13 eq131193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131193
  have eq131523 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq131302 X0
       have i₂ := eq92839 X0
       grind)
    | exact superpose eq92839 eq131302
    | exact resolve eq131302 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92839 eq131302
  have eq131796 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ x = y := by
    first
    | (have i₁ := eq123376
       have i₂ := eq131523 (M.op y x)
       grind)
    | exact superpose eq131523 eq123376
    | exact resolve eq123376 eq131523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123376
  have eq132010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq131796
       have i₂ := eq87169 y
       grind)
    | exact superpose eq87169 eq131796
    | exact resolve eq131796 eq87169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87169 eq131796
  have eq132068 : x = y := by
    first
    | (have r₁ := eq132010
       have r₂ := eq14
       grind)
    | exact resolve eq132010 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132010
  have eq132093 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq132068
       grind)
    | exact superpose eq132068 eq14
    | exact resolve eq14 eq132068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132660 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq131523 X0
       have i₂ := eq132068
       grind)
    | exact superpose eq132068 eq131523
    | exact resolve eq131523 eq132068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131523 eq132068
  have eq132896 : False := by grind
  exact eq132896

/-- `Equation3715`: `x ◇ y = (x ◇ x) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3715 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3715 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3715.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq21 X2 X0
       grind)
    | exact superpose eq21 eq38
    | (have j0 := eq38 X0 X1 X2
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq78 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq81 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq86 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq102 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq78
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq39
    | exact resolve eq39 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq39 (τ X1) X0
       grind)
    | exact superpose eq39 eq17
    | (have j1 := eq39 (τ X1) X0
       grind)
    | exact resolve eq17 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq158 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq86
  have eq172 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq158
    | exact resolve eq158 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq194 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq45 X0 X1 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq45 X2 X1 X2
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq45 X2 X1 X2
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq45 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq42 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq42 x y
       grind)
    | exact superpose eq42 eq14
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X2) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq21
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq431 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq431 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1269 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq360
    | (have j0 := eq360 X0
       have j1 := eq91 X0 X1
       grind)
    | exact resolve eq360 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1285 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1342 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1342
    | (have j0 := eq1342 X0 X1
       grind)
    | exact resolve eq1342 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1476 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq111
    | exact resolve eq111 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1525 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1476 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1476
    | (have j0 := eq1476 X0 X1
       grind)
    | exact resolve eq1476 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1718 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1
       have i₂ := eq1434 X0 X1
       grind)
    | (have i₁ := eq20 X0
       have i₂ := eq1434 (M.op X0 X0) X1
       grind)
    | exact superpose eq1434 eq20
    | (have j1 := eq1434 X0 X1
       grind)
    | exact resolve eq20 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq3104 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq108 X0 X0
       grind)
    | exact superpose eq108 eq22
    | (have j1 := eq108 X0 X0
       grind)
    | exact resolve eq22 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108
  have eq3386 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X0
       have i₂ := eq1718 X0 X1
       grind)
    | exact superpose eq1718 eq447
    | (have j0 := eq447 X0 X1
       have j1 := eq1718 X0 X1
       grind)
    | exact resolve eq447 eq1718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq3431 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3834 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq447 y x
       grind)
    | exact superpose eq447 eq328
    | (have j1 := eq447 y x
       grind)
    | exact resolve eq328 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq1525 y x
       grind)
    | exact superpose eq1525 eq328
    | (have j1 := eq1525 y x
       grind)
    | (have r₁ := eq328
       have r₂ := eq1525 y x
       grind)
    | exact resolve eq328 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq1525
  have eq3839 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq3836
  have eq3841 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq3834
  have eq5707 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq3839
       grind)
    | exact superpose eq3839 eq172
    | exact resolve eq172 eq3839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq3839
  have eq5757 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq5707
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5707
    | exact resolve eq5707 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707
  have eq5758 : x = (k x y) := by grind
  clear eq5757
  have eq6055 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq6056 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6055 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq6113 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq36 y X0 x
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq36
    | (have j0 := eq36 y X0 x
       grind)
    | exact resolve eq36 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq6114 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45 y x X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq45
    | (have j0 := eq45 y x X0
       grind)
    | exact resolve eq45 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq6118 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq447 y x
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq447
    | (have j0 := eq447 y x
       grind)
    | exact resolve eq447 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq6619 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y X0
       grind)
    | exact superpose eq223 eq14
    | (have j1 := eq223 x y X0
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq6788 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6619 X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq6619
    | (have j0 := eq6619 X0
       grind)
    | exact resolve eq6619 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6619
  have eq6849 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | (have j0 := eq312 X1 (τ X0)
       grind)
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq7018 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6849 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq6849
    | (have j0 := eq6849 X0 X1
       grind)
    | exact resolve eq6849 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq6849
  have eq7031 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7018 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7018
    | (have j0 := eq7018 X0 X1
       grind)
    | exact resolve eq7018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7128 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5758
       have i₂ := eq6056 x y
       grind)
    | exact superpose eq6056 eq5758
    | (have j1 := eq6056 x y
       grind)
    | exact resolve eq5758 eq6056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6056
  have eq7301 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115 y x
       have i₂ := eq7128
       grind)
    | exact superpose eq7128 eq115
    | (have j0 := eq115 y x
       grind)
    | (have r₁ := eq115 y x
       have r₂ := eq7128
       grind)
    | (have r₁ := eq115 x y
       have r₂ := eq7128
       grind)
    | exact resolve eq115 eq7128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128
  have eq7314 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq7301
  have eq7810 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq354 y X0 x
       grind)
    | exact superpose eq354 eq14
    | (have j1 := eq354 y X0 x
       grind)
    | exact resolve eq14 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq7847 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7810 X0
       have i₂ := eq5758
       grind)
    | exact superpose eq5758 eq7810
    | (have j0 := eq7810 X0
       grind)
    | exact resolve eq7810 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7810
  have eq9063 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  have eq9764 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6118
       have i₂ := eq6114 y
       grind)
    | exact superpose eq6114 eq6118
    | exact resolve eq6118 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118
  have eq9811 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6113 y
       have i₂ := eq6114 y
       grind)
    | exact superpose eq6114 eq6113
    | exact resolve eq6113 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113 eq6114
  have eq9812 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq9811
  have eq9814 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq9764
  have eq10001 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq9814
  have eq13434 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq3841
       grind)
    | exact superpose eq3841 eq20
    | exact resolve eq20 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3841
  have eq13488 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13434
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq13434
    | exact resolve eq13434 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13434
  have eq14168 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13488
       grind)
    | exact superpose eq13488 eq9
    | exact resolve eq9 eq13488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq14240 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14168
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq14168
    | exact resolve eq14168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14168
  have eq14243 : y = (k y y) := by
    first
    | (have j1 := eq115 y y
       grind)
    | (have r₁ := eq14240
       have r₂ := eq115 y y
       grind)
    | exact resolve eq14240 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14240
  have eq14975 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq360 y
       have i₂ := eq14243
       grind)
    | exact superpose eq14243 eq360
    | (have j0 := eq360 y
       grind)
    | exact resolve eq360 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq14243
  have eq15001 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14975
  have eq30197 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3431 x y
       have i₂ := eq7314
       grind)
    | exact superpose eq7314 eq3431
    | (have j0 := eq3431 x x
       grind)
    | exact resolve eq3431 eq7314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431 eq7314
  have eq30529 : (σ y) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30197
       have r₂ := eq9063
       grind)
    | exact resolve eq30197 eq9063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9063 eq30197
  have eq30874 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30529
       have i₂ := eq9812
       grind)
    | exact superpose eq9812 eq30529
    | exact resolve eq30529 eq9812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9812 eq30529
  have eq30972 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq30874
  have eq34982 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq5758
       have i₂ := eq7031 x y
       grind)
    | exact superpose eq7031 eq5758
    | (have j1 := eq7031 x y
       grind)
    | exact resolve eq5758 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq7031
  have eq35184 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34982
       have r₂ := eq10001
       grind)
    | exact resolve eq34982 eq10001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10001 eq34982
  have eq43337 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6788 X0
       have i₂ := eq30972
       grind)
    | exact superpose eq30972 eq6788
    | (have j0 := eq6788 X0
       grind)
    | exact resolve eq6788 eq30972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52922 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3104 x x
       have i₂ := eq35184
       grind)
    | exact superpose eq35184 eq3104
    | exact resolve eq3104 eq35184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104 eq35184
  have eq52946 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52922 X0
       have j1 := eq43337 X0
       grind)
    | (have r₁ := eq52922 X0
       have r₂ := eq43337 X0
       grind)
    | exact resolve eq52922 eq43337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43337 eq52922
  have eq58335 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15001
       have i₂ := eq52946 (σ y)
       grind)
    | exact superpose eq52946 eq15001
    | exact resolve eq15001 eq52946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52946
  have eq58451 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58335
       grind)
    | exact superpose eq58335 eq14
    | exact resolve eq14 eq58335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58335
  have eq58512 : x = (M.op x y) := by
    first
    | (have r₁ := eq58451
       have r₂ := eq30972
       grind)
    | exact resolve eq58451 eq30972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30972 eq58451
  have eq58536 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6788 X0
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq6788
    | (have j0 := eq6788 X0
       grind)
    | exact resolve eq6788 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6788
  have eq58537 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7847 X0
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq7847
    | (have j0 := eq7847 X0
       grind)
    | exact resolve eq7847 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7847
  have eq58585 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq58537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58537
  have eq58586 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq58536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58536
  have eq58864 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58585 (σ x)
       grind)
    | exact superpose eq58585 eq14
    | exact resolve eq14 eq58585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58868 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq15001
       have i₂ := eq58585 (σ y)
       grind)
    | exact superpose eq58585 eq15001
    | exact resolve eq15001 eq58585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15001 eq58585
  have eq58922 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58868
       have i₂ := eq58586 (σ x)
       grind)
    | exact superpose eq58586 eq58868
    | exact resolve eq58868 eq58586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58586 eq58868
  have eq58923 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58864
       have i₂ := eq58512
       grind)
    | exact superpose eq58512 eq58864
    | exact resolve eq58864 eq58512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58864
  have eq59090 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq58923
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq58923
    | exact resolve eq58923 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58923
  have eq59323 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1285 x X0
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq1285
    | (have j0 := eq1285 x X0
       grind)
    | exact resolve eq1285 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq59334 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq102 (σ x) x
       have i₂ := eq58922
       grind)
    | exact superpose eq58922 eq102
    | exact resolve eq102 eq58922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq58922
  have eq59491 : (τ (σ y)) = (k (τ (σ x)) x) := by
    first
    | (have r₁ := eq59334
       have r₂ := eq59090
       grind)
    | exact resolve eq59334 eq59090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59334
  have eq59499 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq59323 X0
       grind)
    | (have r₁ := eq59323 X0
       have r₂ := eq59090
       grind)
    | exact resolve eq59323 eq59090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59323
  have eq59522 : (k x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq59491
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq59491
    | exact resolve eq59491 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59491
  have eq59538 : y = (k x x) := by
    first
    | (have i₁ := eq59522
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59522
    | exact resolve eq59522 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59522
  have eq59546 : y = (M.op x x) := by
    first
    | (have i₁ := eq59538
       have i₂ := eq59499 x
       grind)
    | exact superpose eq59499 eq59538
    | exact resolve eq59538 eq59499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59499 eq59538
  have eq59601 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq21 x X0
       have i₂ := eq59546
       grind)
    | exact superpose eq59546 eq21
    | exact resolve eq21 eq59546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq60160 : x = (M.op x x) := by
    first
    | (have i₁ := eq58512
       have i₂ := eq59601 x
       grind)
    | exact superpose eq59601 eq58512
    | exact resolve eq58512 eq59601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58512 eq59601
  have eq60446 : x = y := by
    first
    | (have i₁ := eq59546
       have i₂ := eq60160
       grind)
    | exact superpose eq60160 eq59546
    | exact resolve eq59546 eq60160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59546 eq60160
  have eq60715 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq59090
       have i₂ := eq60446
       grind)
    | exact superpose eq60446 eq59090
    | exact resolve eq59090 eq60446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59090 eq60446
  have eq60716 : False := by grind
  exact eq60716

/-- `Equation3715`: `x ◇ y = (x ◇ x) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation3715 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3715 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3715.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X0 X2
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X1 X2
       have i₂ := eq21 X2 X0
       grind)
    | exact superpose eq21 eq38
    | (have j0 := eq38 X0 X1 X2
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq74 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
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
  have eq77 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq79 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq88 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq91 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq102 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq77
  have eq109 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq39
    | exact resolve eq39 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq39 (τ X0) X1
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (τ X0) X1
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq155 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq88 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq88
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq195 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq45 X0 X1 X1
       grind)
    | (have i₁ := eq12 X0 X2
       have i₂ := eq45 X2 X1 X2
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq45 X2 X1 X2
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq45 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 (M.op X1 X1)
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq117
    | (have j0 := eq117 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq117 X1 (M.op X1 X1)
       have r₂ := eq21 X1 X1
       grind)
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | (have j0 := eq42 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X0 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq42
    | exact resolve eq42 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x)
       have i₂ := eq42 x x
       grind)
    | exact superpose eq42 eq20
    | (have j1 := eq42 X0 X0
       grind)
    | exact resolve eq20 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq20
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq20 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X2) X1
       have i₂ := eq42 X0 X2
       grind)
    | exact superpose eq42 eq21
    | (have j1 := eq42 X0 X2
       grind)
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq353
    | (have j0 := eq353 X0 X1
       grind)
    | exact resolve eq353 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq370 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq13 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq13 eq333
    | (have j0 := eq333 X0
       grind)
    | exact resolve eq333 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq390 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq109
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq109 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq109
  have eq414 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq390
    | (have j0 := eq390 X0 X1
       grind)
    | exact resolve eq390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq531 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq36 X0 (σ x) (σ y)
       grind)
    | (have i₁ := eq14
       have i₂ := eq36 (σ y) (σ x) x
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 X0 x (σ y)
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq360 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq360
    | (have j0 := eq360 (M.op X0 X0)
       grind)
    | exact resolve eq360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1343 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq10
    | (have j1 := eq74 X1 X0
       grind)
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1435 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1343
    | (have j0 := eq1343 X0 X1
       grind)
    | exact resolve eq1343 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1477 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1477 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1477
    | (have j0 := eq1477 X0 X1
       grind)
    | exact resolve eq1477 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq3098 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110 x y
       grind)
    | exact superpose eq110 eq14
    | (have j1 := eq110 x y
       grind)
    | exact resolve eq14 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3104 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq110 X0 X0
       grind)
    | exact superpose eq110 eq21
    | (have j1 := eq110 X0 X0
       grind)
    | exact resolve eq21 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3105 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq110 X0 X0
       grind)
    | exact superpose eq110 eq22
    | (have j1 := eq110 X0 X0
       grind)
    | exact resolve eq22 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq3928 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq362 x y
       grind)
    | exact superpose eq362 eq14
    | (have j1 := eq362 x x
       grind)
    | exact resolve eq14 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq6309 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq155 X1 (σ X0)
       grind)
    | exact superpose eq155 eq13
    | (have j1 := eq155 X1 (σ X0)
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6368 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6309 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6309
    | (have j0 := eq6309 X0 X1
       grind)
    | exact resolve eq6309 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309
  have eq6953 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq6954 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6953 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6953
  have eq7585 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y X0
       grind)
    | exact superpose eq223 eq14
    | (have j1 := eq223 y x X0
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq9238 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq354 x X0 y
       grind)
    | exact superpose eq354 eq14
    | (have j1 := eq354 y X0 x
       grind)
    | exact resolve eq14 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq14152 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq312 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq312 X0 X1
       grind)
    | exact superpose eq312 eq9
    | (have j1 := eq312 X0 X1
       grind)
    | exact resolve eq9 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq14233 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14152 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14152
    | (have j0 := eq14152 X0 X1
       grind)
    | exact resolve eq14152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14152
  have eq15698 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq14
    | (have j1 := eq414 x y
       grind)
    | exact resolve eq14 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq15781 : y = (k x y) := by
    first
    | (have j1 := eq1526 x y
       grind)
    | (have r₁ := eq15698
       have r₂ := eq1526 x y
       grind)
    | exact resolve eq15698 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq15698
  have eq16481 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16484 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq36 x X0 y
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq36
    | (have j0 := eq36 y X0 x
       grind)
    | exact resolve eq36 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq16485 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45 x y X0
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq45
    | (have j0 := eq45 y x X0
       grind)
    | exact resolve eq45 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq16497 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1435 x y
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq1435
    | (have j0 := eq1435 x y
       grind)
    | exact resolve eq1435 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16500 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6954 x y
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq6954
    | (have j0 := eq6954 x y
       grind)
    | exact resolve eq6954 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17227 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq16481
       grind)
    | exact superpose eq16481 eq1285
    | exact resolve eq1285 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq19894 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq16500
  have eq21640 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16481
       have i₂ := eq16484 y
       grind)
    | exact superpose eq16484 eq16481
    | exact resolve eq16481 eq16484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16481
  have eq21641 : y ≠ (M.op x x) ∨ y = (M.op x y) := by grind
  have eq21642 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq21640
  have eq23090 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117 y x
       have i₂ := eq21642
       grind)
    | exact superpose eq21642 eq117
    | (have j0 := eq117 y x
       grind)
    | (have r₁ := eq117 y x
       have r₂ := eq21642
       grind)
    | (have r₁ := eq117 x y
       have r₂ := eq21642
       grind)
    | exact resolve eq117 eq21642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21642
  have eq23101 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq23090
  have eq24474 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1435 y x
       have i₂ := eq23101
       grind)
    | exact superpose eq23101 eq1435
    | (have j0 := eq1435 y x
       grind)
    | exact resolve eq1435 eq23101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23101
  have eq24481 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24474
       have r₂ := eq21641
       grind)
    | exact resolve eq24474 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24474
  have eq25453 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16484 y
       have i₂ := eq16485 y
       grind)
    | exact superpose eq16485 eq16484
    | exact resolve eq16484 eq16485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16485
  have eq25454 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq25453
  have eq27112 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq370 (τ X0)
       have i₂ := eq321 X0 (τ X0) (k (τ X0) (τ X0))
       grind)
    | exact superpose eq321 eq370
    | (have j0 := eq370 (τ X0)
       have j1 := eq321 X0 (τ X0) (k (τ X0) (τ X0))
       grind)
    | exact resolve eq370 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq370
  have eq27223 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq27112 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27112
    | (have j0 := eq27112 X0
       grind)
    | exact resolve eq27112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27112
  have eq27445 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq27223 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq27223
    | (have j0 := eq27223 X0
       grind)
    | exact resolve eq27223 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27223
  have eq27565 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq27445 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27445
    | (have j0 := eq27445 X0
       grind)
    | exact resolve eq27445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27445
  have eq27614 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq27565 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27565
    | (have j0 := eq27565 X0
       grind)
    | exact resolve eq27565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27565
  have eq27626 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27614 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27614
    | (have j0 := eq27614 X0
       grind)
    | exact resolve eq27614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27614
  have eq27630 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27626 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq27626
    | (have j0 := eq27626 X0
       grind)
    | exact resolve eq27626 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq27626
  have eq27633 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27630 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27630
    | (have j0 := eq27630 X0
       grind)
    | exact resolve eq27630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27630
  have eq27634 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq27633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27633
  have eq33502 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq248 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq248
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq248 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq248 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq248 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq33697 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33502
  have eq37614 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24481
       have i₂ := eq25454
       grind)
    | exact superpose eq25454 eq24481
    | exact resolve eq24481 eq25454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24481 eq25454
  have eq37721 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37614
  have eq39339 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1397 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq39340 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq39339 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39339
    | (have j0 := eq39339 X0
       grind)
    | exact resolve eq39339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39339
  have eq39507 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3098
       have i₂ := eq6954 x y
       grind)
    | exact superpose eq6954 eq3098
    | (have j1 := eq6954 x y
       grind)
    | exact resolve eq3098 eq6954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq39518 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39507
  have eq39682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3928
       have i₂ := eq1435 x y
       grind)
    | exact superpose eq1435 eq3928
    | (have j1 := eq1435 x y
       grind)
    | (have r₁ := eq3928
       have r₂ := eq1435 x y
       grind)
    | exact resolve eq3928 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq39692 : (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by grind
  clear eq39682
  have eq39746 : (k x x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq39692
       grind)
    | exact superpose eq39692 eq9
    | exact resolve eq9 eq39692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39692
  have eq39867 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39746
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq39746
    | exact resolve eq39746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39746
  have eq40108 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6954 x x
       have i₂ := eq39867
       grind)
    | exact superpose eq39867 eq6954
    | (have j0 := eq6954 x x
       grind)
    | exact resolve eq6954 eq39867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39867
  have eq40110 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq40108
  have eq40692 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y
       have i₂ := eq40110
       grind)
    | exact superpose eq40110 eq20
    | exact resolve eq20 eq40110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40110
  have eq40733 : x = (k x x) := by
    first
    | (have j1 := eq117 x x
       grind)
    | (have r₁ := eq40692
       have r₂ := eq117 x x
       grind)
    | exact resolve eq40692 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40692
  have eq41062 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq360 x
       have i₂ := eq40733
       grind)
    | exact superpose eq40733 eq360
    | (have j0 := eq360 x
       grind)
    | exact resolve eq360 eq40733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq41088 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6954 x x
       have i₂ := eq40733
       grind)
    | exact superpose eq40733 eq6954
    | (have j0 := eq6954 x x
       grind)
    | exact resolve eq6954 eq40733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40733
  have eq41090 : x = (M.op x x) := by grind
  clear eq41088
  have eq41096 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41062
  have eq41229 : x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21641
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq21641
    | exact resolve eq21641 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21641
  have eq51131 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39340 X0
       have i₂ := eq33697 X0 X0
       grind)
    | exact superpose eq33697 eq39340
    | (have j0 := eq39340 X0
       have j1 := eq33697 X0 X0
       grind)
    | (have r₁ := eq39340 X0
       have r₂ := eq33697 X0 X0
       grind)
    | exact resolve eq39340 eq33697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33697
  have eq51148 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39340 (σ X0)
       have i₂ := eq155 X0 (σ X0)
       grind)
    | exact superpose eq155 eq39340
    | (have j0 := eq39340 (σ X0)
       have j1 := eq155 X0 (σ X0)
       grind)
    | (have r₁ := eq39340 (σ X0)
       have r₂ := eq155 X0 (σ X0)
       grind)
    | exact resolve eq39340 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq51169 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq51148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51148
  have eq51185 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq51169 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51169
    | (have j0 := eq51169 X0
       grind)
    | exact resolve eq51169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51169
  have eq51189 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq51131 X0
       have j1 := eq39340 X0
       grind)
    | (have r₁ := eq51131 X0
       have r₂ := eq39340 X0
       grind)
    | exact resolve eq51131 eq39340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39340 eq51131
  have eq51194 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq51185 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51185
    | (have j0 := eq51185 X0
       grind)
    | exact resolve eq51185 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185
  have eq61138 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq531 (σ x)
       have i₂ := eq17227
       grind)
    | exact superpose eq17227 eq531
    | (have j0 := eq531 (σ x)
       grind)
    | exact resolve eq531 eq17227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq17227
  have eq61256 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61138
       have r₂ := eq37721
       grind)
    | exact resolve eq61138 eq37721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37721 eq61138
  have eq61265 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61256
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq61256
    | exact resolve eq61256 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61256
  have eq61266 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61265
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq61265
    | exact resolve eq61265 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61265
  have eq63179 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3104 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq3104
    | exact resolve eq3104 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3104
  have eq63521 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63179 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63179
    | (have j0 := eq63179 X0 X1
       grind)
    | exact resolve eq63179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63179
  have eq63534 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63521 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63521
    | (have j0 := eq63521 X0 X1
       grind)
    | exact resolve eq63521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63521
  have eq64608 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61266
       grind)
    | exact superpose eq61266 eq14
    | exact resolve eq14 eq61266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65725 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq7585 X0
       have i₂ := eq15781
       grind)
    | exact superpose eq15781 eq7585
    | (have j0 := eq7585 X0
       grind)
    | exact resolve eq7585 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7585 eq15781
  have eq65910 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9238 X0
       have i₂ := eq6954 x y
       grind)
    | exact superpose eq6954 eq9238
    | (have j0 := eq9238 X0
       have j1 := eq6954 x y
       grind)
    | exact resolve eq9238 eq6954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6954
  have eq65911 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9238 X0
       have i₂ := eq1435 x y
       grind)
    | exact superpose eq1435 eq9238
    | (have j0 := eq9238 X0
       have j1 := eq1435 x y
       grind)
    | (have r₁ := eq9238 X0
       have r₂ := eq1435 x y
       grind)
    | exact resolve eq9238 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9238
  have eq65921 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq65911 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65911
  have eq65922 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65910
  have eq90250 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63534 X0 (k X0 X0)
       have i₂ := eq27634 X0
       grind)
    | exact superpose eq27634 eq63534
    | (have j0 := eq63534 X0 x
       have j1 := eq27634 X0
       grind)
    | exact resolve eq63534 eq27634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27634
  have eq90512 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq90250 X0
       have j1 := eq117 X0 X0
       grind)
    | (have r₁ := eq90250 x
       have r₂ := eq117 x x
       grind)
    | exact resolve eq90250 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq90250
  have eq107805 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65921 (σ x)
       grind)
    | exact superpose eq65921 eq14
    | exact resolve eq14 eq65921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65921
  have eq107817 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq107805
       have i₂ := eq41096
       grind)
    | exact superpose eq41096 eq107805
    | exact resolve eq107805 eq41096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107805
  have eq107852 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq107817
       have i₂ := eq16497
       grind)
    | exact superpose eq16497 eq107817
    | exact resolve eq107817 eq16497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16497 eq107817
  have eq107862 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq107852
  have eq108005 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65922 (σ x)
       grind)
    | exact superpose eq65922 eq14
    | exact resolve eq14 eq65922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65922
  have eq108017 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108005
       have i₂ := eq41096
       grind)
    | exact superpose eq41096 eq108005
    | exact resolve eq108005 eq41096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108005
  have eq108055 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ x = y ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq108017
       have i₂ := eq16484 X0
       grind)
    | exact superpose eq16484 eq108017
    | (have j1 := eq16484 X0
       grind)
    | exact resolve eq108017 eq16484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16484
  have eq108064 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108017
       have i₂ := eq39518
       grind)
    | exact superpose eq39518 eq108017
    | exact resolve eq108017 eq39518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39518 eq108017
  have eq108069 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq108064
  have eq108404 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51194 X1
       have i₂ := eq1435 X0 X1
       grind)
    | (have i₁ := eq51194 X0
       have i₂ := eq1435 (M.op X0 X0) X1
       grind)
    | exact superpose eq1435 eq51194
    | (have j1 := eq1435 X0 X1
       grind)
    | exact resolve eq51194 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435
  have eq112630 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14233 x y
       grind)
    | exact superpose eq14233 eq14
    | (have j1 := eq14233 x y
       grind)
    | exact resolve eq14 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233
  have eq112634 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq108404 x y
       grind)
    | (have r₁ := eq112630
       have r₂ := eq108404 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq112630
       have r₂ := eq108404 (k x y) (M.op x y)
       grind)
    | (have r₁ := eq112630
       have r₂ := eq108404 x y
       grind)
    | exact resolve eq112630 eq108404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108404 eq112630
  have eq112710 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq63534 y x
       have i₂ := eq112634
       grind)
    | exact superpose eq112634 eq63534
    | exact resolve eq63534 eq112634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63534
  have eq112713 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90512 y
       have i₂ := eq112634
       grind)
    | exact superpose eq112634 eq90512
    | exact resolve eq90512 eq112634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90512
  have eq112741 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6368 y y
       have i₂ := eq112634
       grind)
    | exact superpose eq112634 eq6368
    | exact resolve eq6368 eq112634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368 eq112634
  have eq112757 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq112741
  have eq112773 : x = (M.op y y) := by
    first
    | (have r₁ := eq112757
       have r₂ := eq107862
       grind)
    | exact resolve eq112757 eq107862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107862 eq112757
  have eq112793 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq112713
       have r₂ := eq19894
       grind)
    | exact resolve eq112713 eq19894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19894 eq112713
  have eq112794 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq112710 X0
       have j1 := eq108055 X0
       grind)
    | (have r₁ := eq112710 X0
       have r₂ := eq108055 X0
       grind)
    | exact resolve eq112710 eq108055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108055 eq112710
  have eq112825 : x = (M.op x y) := by
    first
    | (have r₁ := eq112793
       have r₂ := eq108069
       grind)
    | exact resolve eq112793 eq108069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108069 eq112793
  have eq112864 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq112773
       grind)
    | exact superpose eq112773 eq21
    | exact resolve eq21 eq112773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq112865 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq112773
       grind)
    | exact superpose eq112773 eq22
    | exact resolve eq22 eq112773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq112773
  have eq113036 : (σ x) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64608
       have i₂ := eq112825
       grind)
    | exact superpose eq112825 eq64608
    | exact resolve eq64608 eq112825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64608 eq112825
  have eq115569 : (σ y) = (σ (M.op y x)) ∨ (k y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq51194 y
       have i₂ := eq112794 y
       grind)
    | exact superpose eq112794 eq51194
    | exact resolve eq51194 eq112794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51194 eq112794
  have eq115854 : (σ y) = (σ (M.op x x)) ∨ (k y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq115569
       have i₂ := eq112865 x
       grind)
    | exact superpose eq112865 eq115569
    | exact resolve eq115569 eq112865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115569
  have eq115974 : (σ x) = (σ y) ∨ (k y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq115854
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq115854
    | exact resolve eq115854 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115854
  have eq116046 : (k y y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq115974
       have r₂ := eq113036
       grind)
    | exact resolve eq115974 eq113036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115974
  have eq116075 : (M.op x x) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq116046
       have i₂ := eq112865 x
       grind)
    | exact superpose eq112865 eq116046
    | exact resolve eq116046 eq112865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116046
  have eq116096 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq116075
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq116075
    | exact resolve eq116075 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116075
  have eq116177 : ∀ X0 : G, x = y ∨ (M.op y X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq91 y X0
       have i₂ := eq116096
       grind)
    | exact superpose eq116096 eq91
    | (have j0 := eq91 y X0
       grind)
    | exact resolve eq91 eq116096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq116096
  have eq116297 : ∀ X0 : G, x = y ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq116177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116177
  have eq116313 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq116297 X0
       have i₂ := eq112865 X0
       grind)
    | exact superpose eq112865 eq116297
    | exact resolve eq116297 eq112865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116297
  have eq117221 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3105 y x
       have i₂ := eq116313 y
       grind)
    | exact superpose eq116313 eq3105
    | exact resolve eq3105 eq116313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105 eq116313
  have eq117408 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq117221 X0
       have i₂ := eq112864 x
       grind)
    | exact superpose eq112864 eq117221
    | exact resolve eq117221 eq112864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117221
  have eq117456 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq117408 X0
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq117408
    | exact resolve eq117408 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117408
  have eq117473 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq117456 X0
       have j1 := eq65725 X0
       grind)
    | (have r₁ := eq117456 X0
       have r₂ := eq65725 X0
       grind)
    | exact resolve eq117456 eq65725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65725 eq117456
  have eq121422 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op (τ (σ y)) (τ (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq51189 (σ y)
       have i₂ := eq117473 (σ y)
       grind)
    | exact superpose eq117473 eq51189
    | (have j0 := eq51189 (σ y)
       grind)
    | exact resolve eq51189 eq117473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51189 eq117473
  have eq121509 : (σ y) = (σ (M.op y y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121422
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq121422
    | exact resolve eq121422 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121422
  have eq121537 : (σ y) = (σ (M.op y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121509
       have i₂ := eq112864 y
       grind)
    | exact superpose eq112864 eq121509
    | exact resolve eq121509 eq112864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121509
  have eq121551 : (σ y) = (σ (M.op x x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121537
       have i₂ := eq112865 x
       grind)
    | exact superpose eq112865 eq121537
    | exact resolve eq121537 eq112865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112865 eq121537
  have eq121561 : (σ x) = (σ y) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121551
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq121551
    | exact resolve eq121551 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121551
  have eq121567 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq121561
       have r₂ := eq113036
       grind)
    | exact resolve eq121561 eq113036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113036 eq121561
  have eq121580 : (σ y) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121567
       have i₂ := eq61266
       grind)
    | exact superpose eq61266 eq121567
    | (have r₁ := eq121567
       have r₂ := eq61266
       grind)
    | exact resolve eq121567 eq61266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61266 eq121567
  have eq121604 : x = y ∨ y = (M.op x y) := by grind
  clear eq121580
  have eq121614 : y = (M.op x y) := by
    first
    | (have r₁ := eq121604
       have r₂ := eq41229
       grind)
    | exact resolve eq121604 eq41229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41229 eq121604
  have eq121618 : y = (M.op x x) := by
    first
    | (have i₁ := eq121614
       have i₂ := eq112864 x
       grind)
    | exact superpose eq112864 eq121614
    | exact resolve eq121614 eq112864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112864 eq121614
  have eq121619 : x = y := by
    first
    | (have i₁ := eq121618
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq121618
    | exact resolve eq121618 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121618
  have eq121647 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq121619
       grind)
    | exact superpose eq121619 eq14
    | exact resolve eq14 eq121619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121619
  have eq121772 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121647
       have i₂ := eq41090
       grind)
    | exact superpose eq41090 eq121647
    | exact resolve eq121647 eq41090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41090 eq121647
  have eq121777 : False := by grind
  exact eq121777

/-- `Equation3716`: `x ◇ y = (x ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3716 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3716 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3716.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X2
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X0) (M.op X1 x)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq19 X0 x X2
       have i₂ := eq8 X2 X0 x
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq21 X0 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq37 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq22 X0 (M.op X1 X2)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq103 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq145 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq38 (τ X0) X1
       grind)
    | exact superpose eq38 eq17
    | (have j1 := eq38 (τ X0) X1
       grind)
    | exact resolve eq17 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq153 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq161 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq108
  have eq175 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq161 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq161
    | exact resolve eq161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq203 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 (M.op X1 X2) X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq153
    | (have j0 := eq153 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq153 (M.op X0 X0) X0
       have r₂ := eq56 X0 X0 X0
       grind)
    | exact resolve eq153 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X3 ∨ (M.op X3 X1) = (k X1 X3) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X3
       have i₂ := eq37 X0 X1 X1 X2
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 X3
       have j1 := eq37 X3 X1 X2 X3
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq297 : ∀ X0 X1 X3 : G, (M.op X0 X1) = X3 ∨ (M.op X3 X1) = (k X1 X3) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq233 X0 X1 x X3
       have i₂ := eq56 X0 X1 x
       grind)
    | exact superpose eq56 eq233
    | (have j0 := eq233 X3 X1 x X3
       grind)
    | exact resolve eq233 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq462 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq175
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq175 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq466 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq20
    | (have j1 := eq42 X0 X1
       grind)
    | exact resolve eq20 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (σ X2) (σ X2)
       have i₂ := eq42 X0 X2
       grind)
    | exact superpose eq42 eq56
    | (have j1 := eq42 X0 X2
       grind)
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq479 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq482 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq462
    | (have j0 := eq462 X0 X1
       grind)
    | exact resolve eq462 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq616 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq36 (σ y) (σ x) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq36 X0 (σ x) (σ y)
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 (σ y) x X0
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1600 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1723 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1600 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1600
    | (have j0 := eq1600 X0 X1
       grind)
    | exact resolve eq1600 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1773 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq149
    | exact resolve eq149 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1825 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1773 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1773
    | (have j0 := eq1773 X0 X1
       grind)
    | exact resolve eq1773 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq2975 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq145 y x
       grind)
    | exact superpose eq145 eq14
    | (have j1 := eq145 y x
       grind)
    | exact resolve eq14 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3773 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq479 x y
       grind)
    | exact superpose eq479 eq14
    | (have j1 := eq479 x x
       grind)
    | exact resolve eq14 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq6999 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq297 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq7000 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6999 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6999
  have eq29506 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq14
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq14 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq29607 : y = (k y x) := by
    first
    | (have j1 := eq1825 x y
       grind)
    | (have r₁ := eq29506
       have r₂ := eq1825 x y
       grind)
    | exact resolve eq29506 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq29506
  have eq30733 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7000 y x
       have i₂ := eq29607
       grind)
    | exact superpose eq29607 eq7000
    | (have j0 := eq7000 y x
       grind)
    | exact resolve eq7000 eq29607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36624 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 x y
       have i₂ := eq30733
       grind)
    | exact superpose eq30733 eq56
    | exact resolve eq56 eq30733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30733
  have eq38296 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq203 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq38302 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38296 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq38296 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq38296
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq38296 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38296
  have eq40183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2975
       have i₂ := eq38302 x y
       grind)
    | exact superpose eq38302 eq2975
    | (have j1 := eq38302 x y
       grind)
    | exact resolve eq2975 eq38302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975 eq38302
  have eq40192 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq40183
  have eq40320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3773
       have i₂ := eq1723 x y
       grind)
    | exact superpose eq1723 eq3773
    | (have j1 := eq1723 x y
       grind)
    | (have r₁ := eq3773
       have r₂ := eq1723 x y
       grind)
    | exact resolve eq3773 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723 eq3773
  have eq40328 : (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by grind
  clear eq40320
  have eq40358 : (k x x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq40328
       grind)
    | exact superpose eq40328 eq9
    | exact resolve eq9 eq40328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40328
  have eq40399 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40358
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq40358
    | exact resolve eq40358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40358
  have eq40494 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7000 x x
       have i₂ := eq40399
       grind)
    | exact superpose eq40399 eq7000
    | (have j0 := eq7000 x x
       grind)
    | exact resolve eq7000 eq40399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40399
  have eq40496 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq40494
  have eq40559 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y
       have i₂ := eq40496
       grind)
    | exact superpose eq40496 eq20
    | exact resolve eq20 eq40496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40496
  have eq40610 : x = (k x x) := by
    first
    | (have j1 := eq153 x x
       grind)
    | (have r₁ := eq40559
       have r₂ := eq153 x x
       grind)
    | exact resolve eq40559 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq40559
  have eq40654 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq475 x
       have i₂ := eq40610
       grind)
    | exact superpose eq40610 eq475
    | (have j0 := eq475 x
       grind)
    | exact resolve eq475 eq40610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq40682 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7000 x x
       have i₂ := eq40610
       grind)
    | exact superpose eq40610 eq7000
    | (have j0 := eq7000 x x
       grind)
    | exact resolve eq7000 eq40610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000 eq40610
  have eq40684 : x = (M.op x x) := by grind
  clear eq40682
  have eq40690 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq40654
  have eq42676 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq36624
  have eq42679 : x = (M.op x y) := by
    first
    | (have r₁ := eq42676
       have r₂ := eq40684
       grind)
    | exact resolve eq42676 eq40684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40684 eq42676
  have eq42735 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40192
       have i₂ := eq42679
       grind)
    | exact superpose eq42679 eq40192
    | exact resolve eq40192 eq42679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40192
  have eq42797 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq616 (σ x)
       have i₂ := eq40690
       grind)
    | exact superpose eq40690 eq616
    | (have j0 := eq616 (σ x)
       grind)
    | exact resolve eq616 eq40690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq42798 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq42797
       have i₂ := eq42679
       grind)
    | exact superpose eq42679 eq42797
    | exact resolve eq42797 eq42679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42797
  have eq42799 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq42798
  have eq42803 : (σ (k x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq42799
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq42799
    | exact resolve eq42799 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42799
  have eq43680 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (k x y))) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (σ y) (σ x)
       have i₂ := eq42803
       grind)
    | exact superpose eq42803 eq56
    | exact resolve eq56 eq42803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq42803
  have eq44536 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq43680 X0
       have i₂ := eq42735
       grind)
    | exact superpose eq42735 eq43680
    | exact resolve eq43680 eq42735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42735 eq43680
  have eq45871 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq473 x X0 y
       grind)
    | exact superpose eq473 eq14
    | (have j1 := eq473 y X0 x
       grind)
    | exact resolve eq14 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq45879 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq45871 X0
       have i₂ := eq29607
       grind)
    | exact superpose eq29607 eq45871
    | (have j0 := eq45871 X0
       grind)
    | exact resolve eq45871 eq29607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29607 eq45871
  have eq45892 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq45879 X0
       have i₂ := eq42679
       grind)
    | exact superpose eq42679 eq45879
    | (have j0 := eq45879 X0
       grind)
    | exact resolve eq45879 eq42679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45879
  have eq45893 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq45892 X0
       have j1 := eq44536 X0
       grind)
    | (have r₁ := eq45892 X0
       have r₂ := eq44536 X0
       grind)
    | exact resolve eq45892 eq44536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44536 eq45892
  have eq46087 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq45893 (σ x)
       grind)
    | exact superpose eq45893 eq14
    | exact resolve eq14 eq45893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45893
  have eq46130 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq46087
       have i₂ := eq40690
       grind)
    | exact superpose eq40690 eq46087
    | exact resolve eq46087 eq40690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40690 eq46087
  have eq46270 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq46130
       have i₂ := eq42679
       grind)
    | exact superpose eq42679 eq46130
    | exact resolve eq46130 eq42679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42679 eq46130
  have eq46271 : False := by grind
  exact eq46271

/-- `Equation3718`: `x ◇ y = (x ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation3718 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3718 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3718.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X1 X2
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X3 X1) (M.op X0 X0)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X2 X1) = (k (M.op X2 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 X1) (M.op X0 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op X2 X1) (M.op X0 X0)
       grind)
    | (have r₁ := eq11 (M.op X2 X1) (M.op X1 X1)
       have r₂ := eq8 X1 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X3 X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq18 x X1 X2 X3
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X1) X2 X3
       have i₂ := eq20 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X0 X1 X2 x
       have i₂ := eq20 X2 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq20 eq27
    | exact resolve eq27 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq21 X1 X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq59 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq78 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq52
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq100 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq34
    | (have j0 := eq34 X1 X0
       have j1 := eq34 X1 X0
       grind)
    | exact resolve eq34 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) X2 (σ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq20
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq20 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq34 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq11 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (σ X2)) = (M.op X1 (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X2) X1 (σ X0)
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq20
    | (have j1 := eq34 X2 X0
       grind)
    | exact resolve eq20 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq34 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq11 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq113
    | (have j0 := eq113 X0 X1
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq11
    | (have j0 := eq11 X2 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq11 X2 (M.op (M.op X0 X2) X2)
       have r₂ := eq29 X0 X2 X2
       grind)
    | exact resolve eq11 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq253 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq42 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq290 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq59 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq253 (σ X0)
       grind)
    | exact superpose eq253 eq59
    | exact resolve eq59 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq291 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq253 (τ X0)
       grind)
    | exact superpose eq253 eq15
    | exact resolve eq15 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq291
    | exact resolve eq291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq293 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq290
    | exact resolve eq290 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq481 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq112 (M.op X0 X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq112
    | (have j0 := eq112 (M.op X0 X0)
       grind)
    | exact resolve eq112 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq488 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq505 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq538 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq505 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq505
    | (have j0 := eq505 X0 X1
       grind)
    | exact resolve eq505 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq650 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq34
    | (have j0 := eq34 X1 X0
       have j1 := eq114 X0 X1
       grind)
    | exact resolve eq34 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 y x
       grind)
    | exact superpose eq114 eq14
    | (have j1 := eq114 y x
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq694 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq697 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq766 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 (τ X0) (τ X1) X2
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq102
    | (have j0 := eq102 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq102 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq102
  have eq812 : ∀ X0 X1 X2 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq766 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq766
    | (have j0 := eq766 X0 X1 X2
       grind)
    | exact resolve eq766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq816 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq812 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq812
    | (have j0 := eq812 X0 X1 X2
       grind)
    | exact resolve eq812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq818 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 X1) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq816 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq816
    | (have j0 := eq816 X0 X1 X2
       grind)
    | exact resolve eq816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq819 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq818 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq818
    | (have j0 := eq818 X0 X1 X2
       grind)
    | exact resolve eq818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq1021 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (M.op (σ X2) (σ X1)) = (σ (k X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X2 X0
       have i₂ := eq109 X1 (σ X0) X2
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq109 X0 (σ X1) X2
       grind)
    | exact superpose eq109 eq34
    | (have j0 := eq34 X2 X0
       have j1 := eq109 X0 X1 X2
       grind)
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1075 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq109 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1156 : ∀ X0 X1 : G, (σ X0) ≠ (k (σ X0) X1) ∨ (σ (τ X1)) = (σ (k (τ X1) X0)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 (τ X1)
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq117
    | (have j0 := eq117 X0 (τ X1)
       grind)
    | exact resolve eq117 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1166 : ∀ X0 X1 : G, (σ (τ X1)) = (k X1 (σ X0)) ∨ (σ X0) ≠ (k (σ X0) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1156
    | (have j0 := eq1156 X0 X1
       grind)
    | exact resolve eq1156 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1176 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ X0) ≠ (k (σ X0) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1166 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1166
    | (have j0 := eq1166 X0 X1
       grind)
    | exact resolve eq1166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1181 : ∀ X0 X1 : G, (σ X0) ≠ (k (σ X0) X1) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1728 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1778 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1728 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1728
    | (have j0 := eq1728 X0 X1
       grind)
    | exact resolve eq1728 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1786 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1778 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1778
    | (have j0 := eq1778 X0 X1
       grind)
    | exact resolve eq1778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1778
  have eq1789 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1786 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq1786 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq1786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq2577 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq697
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2627 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq2752 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2577 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2779 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1789 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1789
    | exact resolve eq1789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq2917 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2752 X0 (M.op X2 X1)
       have i₂ := eq20 X1 X0 X2
       grind)
    | exact superpose eq20 eq2752
    | (have j0 := eq2752 X0 X1
       grind)
    | exact resolve eq2752 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq666
       have i₂ := eq538 x y
       grind)
    | exact superpose eq538 eq666
    | (have j1 := eq538 x y
       grind)
    | (have r₁ := eq666
       have r₂ := eq538 x y
       grind)
    | exact resolve eq666 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq666
  have eq3030 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq3029
  have eq3081 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 X1)) ∨ (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq2779 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact superpose eq2779 eq68
    | (have j1 := eq2779 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq68 eq2779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2779
  have eq3165 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3081 X0 X1
       have j1 := eq11 (M.op X1 X1) (M.op X0 X1)
       grind)
    | (have r₁ := eq3081 X0 X1
       have r₂ := eq11 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq3081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3382 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq3030
       grind)
    | exact superpose eq3030 eq9
    | exact resolve eq9 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3439 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3382
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3382
    | exact resolve eq3382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3570 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq3439
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq3439
       grind)
    | exact resolve eq11 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3578 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2752 y x
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq2752
    | (have j0 := eq2752 y x
       grind)
    | (have r₁ := eq2752 y x
       have r₂ := eq3439
       grind)
    | (have r₁ := eq2752 x y
       have r₂ := eq3439
       grind)
    | exact resolve eq2752 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3580 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq3578
  have eq3582 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq3570
  have eq3583 : y = (k y x) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq3580
       have r₂ := eq11 y x
       grind)
    | exact resolve eq3580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3580
  have eq3584 : x = (k x y) := by
    first
    | (have j1 := eq2752 x y
       grind)
    | (have r₁ := eq3582
       have r₂ := eq2752 x y
       grind)
    | exact resolve eq3582 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752 eq3582
  have eq3714 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq685 X1 X0
       grind)
    | exact superpose eq685 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq685 X1 X0
       grind)
    | exact resolve eq11 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq3729 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3714 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3714
    | (have j0 := eq3714 X0 X1
       grind)
    | exact resolve eq3714 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3714
  have eq3730 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq3757 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq819 x y X0
       have i₂ := eq3584
       grind)
    | exact superpose eq3584 eq819
    | (have j0 := eq819 x y x
       grind)
    | exact resolve eq819 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq3584
  have eq5079 : y = (k y (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq253 y
       have i₂ := eq3757 y
       grind)
    | exact superpose eq3757 eq253
    | exact resolve eq253 eq3757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq5129 : y = (k y (M.op y x)) := by
    first
    | (have j1 := eq2917 y x y
       grind)
    | (have r₁ := eq5079
       have r₂ := eq2917 y x x
       grind)
    | exact resolve eq5079 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079
  have eq5160 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1181 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq292 (σ X0)
       grind)
    | exact superpose eq292 eq1181
    | (have j0 := eq1181 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       grind)
    | (have r₁ := eq1181 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have r₂ := eq292 (σ X0)
       grind)
    | exact resolve eq1181 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq1181
  have eq5179 : ∀ X0 : G, (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5192 : ∀ X0 : G, (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5179 X0
       have j1 := eq2627 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       grind)
    | (have r₁ := eq5179 x
       have r₂ := eq2627 (σ (M.op (τ (σ x)) (τ (σ x)))) x
       grind)
    | exact resolve eq5179 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627 eq5179
  have eq5206 : ∀ X0 : G, (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq5192 X0
       have i₂ := eq13 (M.op (τ (σ X0)) (τ (σ X0))) X0
       grind)
    | exact superpose eq13 eq5192
    | exact resolve eq5192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5192
  have eq5214 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5206 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq5206
    | exact resolve eq5206 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5222 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5129
       have i₂ := eq3757 X0
       grind)
    | exact superpose eq3757 eq5129
    | (have j1 := eq3757 X0
       grind)
    | exact resolve eq5129 eq3757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129
  have eq5301 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq178 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq5360 : ∀ X0 : G, y = (k y (M.op (M.op X0 y) x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq5301 y X0
       have i₂ := eq3757 (M.op X0 y)
       grind)
    | exact superpose eq3757 eq5301
    | exact resolve eq5301 eq3757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5301
  have eq5404 : ∀ X0 : G, y = (k y (M.op (M.op X0 y) x)) := by
    intro X0
    first
    | (have j0 := eq5360 X0
       have j1 := eq2917 y x (M.op X0 y)
       grind)
    | (have r₁ := eq5360 X0
       have r₂ := eq2917 y x x
       grind)
    | exact resolve eq5360 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5360
  have eq5679 : ∀ X0 : G, y = (k y (M.op (M.op X0 x) x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq5404 X0
       have i₂ := eq3757 X0
       grind)
    | exact superpose eq3757 eq5404
    | exact resolve eq5404 eq3757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404
  have eq5702 : ∀ X0 : G, y = (k y (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have j0 := eq5679 X0
       have j1 := eq2917 y x (M.op X0 x)
       grind)
    | (have r₁ := eq5679 X0
       have r₂ := eq2917 y x x
       grind)
    | exact resolve eq5679 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917 eq5679
  have eq5960 : y = (k y (M.op x x)) := by
    first
    | (have i₁ := eq5702 x
       have i₂ := eq21 x x
       grind)
    | exact superpose eq21 eq5702
    | exact resolve eq5702 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5702
  have eq9396 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y y
       have i₂ := eq5222 X0
       grind)
    | exact superpose eq5222 eq12
    | (have j0 := eq12 y y
       have j1 := eq5222 X0
       grind)
    | exact resolve eq12 eq5222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5222
  have eq9429 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq9396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9396
  have eq9635 : y ≠ (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq9429
  have eq10307 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) X1)) ∨ (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1075 (M.op X0 X0) X1
       have i₂ := eq488 X0
       grind)
    | exact superpose eq488 eq1075
    | (have j0 := eq1075 (M.op X0 X0) X1
       grind)
    | exact resolve eq1075 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq10323 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10307 X0 X1
       have j1 := eq114 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq10307 X0 X0
       have r₂ := eq114 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10307 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10307
  have eq12126 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (σ (k (M.op x x) y)) := by
    first
    | (have i₁ := eq3730 y (M.op x x)
       have i₂ := eq5960
       grind)
    | exact superpose eq5960 eq3730
    | (have j0 := eq3730 y (M.op x x)
       grind)
    | exact resolve eq3730 eq5960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730 eq5960
  have eq12161 : (σ (M.op x x)) = (σ (k (M.op x x) y)) := by grind
  clear eq12126
  have eq18569 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) X2 (σ (M.op X0 X0))
       have i₂ := eq10323 X0 X1
       grind)
    | exact superpose eq10323 eq20
    | exact resolve eq20 eq10323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10323
  have eq18938 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18569 X0 (M.op X2 X0) X1
       have i₂ := eq3165 X2 X0
       grind)
    | exact superpose eq3165 eq18569
    | exact resolve eq18569 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq18967 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18569 X0 X0 X1
       have i₂ := eq5214 X0
       grind)
    | exact superpose eq5214 eq18569
    | exact resolve eq18569 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq18968 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq18569 x y X0
       have i₂ := eq12161
       grind)
    | exact superpose eq12161 eq18569
    | exact resolve eq18569 eq12161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12161 eq18569
  have eq19194 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18938 X0 X1 X2
       have i₂ := eq18967 X0 X1
       grind)
    | exact superpose eq18967 eq18938
    | exact resolve eq18938 eq18967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18938 eq18967
  have eq20770 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19194 x X0 x
       have i₂ := eq18968 X0
       grind)
    | exact superpose eq18968 eq19194
    | exact resolve eq19194 eq18968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18968 eq19194
  have eq21336 : y = (k y (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq293 y
       have i₂ := eq20770 (σ y)
       grind)
    | exact superpose eq20770 eq293
    | exact resolve eq293 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq21343 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20770 (σ x)
       grind)
    | exact superpose eq20770 eq14
    | exact resolve eq14 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21687 : y = (k y (k (τ (σ y)) x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21336
       have i₂ := eq82 (σ y) x
       grind)
    | exact superpose eq82 eq21336
    | (have j1 := eq82 (σ y) x
       grind)
    | exact resolve eq21336 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq21336
  have eq21748 : y = (k y (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21687
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq21687
    | exact resolve eq21687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21687
  have eq21767 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21748
       have i₂ := eq3583
       grind)
    | exact superpose eq3583 eq21748
    | exact resolve eq21748 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583 eq21748
  have eq21779 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq21767
       have i₂ := eq20770 (σ x)
       grind)
    | exact superpose eq20770 eq21767
    | exact resolve eq21767 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20770 eq21767
  have eq34575 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq21343
       have i₂ := eq21779
       grind)
    | exact superpose eq21779 eq21343
    | exact resolve eq21343 eq21779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21779
  have eq38353 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq34575
       have i₂ := eq3030
       grind)
    | exact superpose eq3030 eq34575
    | (have r₁ := eq34575
       have r₂ := eq3030
       grind)
    | exact resolve eq34575 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030 eq34575
  have eq38354 : y = (k y y) ∨ y = (M.op y x) := by grind
  clear eq38353
  have eq38640 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq38354
       grind)
    | exact superpose eq38354 eq12
    | (have j0 := eq12 y y
       grind)
    | exact resolve eq12 eq38354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38354
  have eq38645 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq38640
  have eq38652 : y = (M.op y y) := by
    first
    | (have r₁ := eq38645
       have r₂ := eq9635
       grind)
    | exact resolve eq38645 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635 eq38645
  have eq38920 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3757 y
       have i₂ := eq38652
       grind)
    | exact superpose eq38652 eq3757
    | exact resolve eq3757 eq38652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757 eq38652
  have eq38964 : y = (M.op y x) := by grind
  clear eq38920
  have eq39541 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20 x X0 y
       have i₂ := eq38964
       grind)
    | exact superpose eq38964 eq20
    | exact resolve eq20 eq38964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38964
  have eq49136 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq1021 X0 X0 X2
       grind)
    | exact superpose eq1021 eq1075
    | (have j0 := eq1075 X0 X1
       have j1 := eq1021 X1 X1 X0
       grind)
    | (have r₁ := eq1075 X0 X0
       have r₂ := eq1021 X0 X1 X0
       grind)
    | (have r₁ := eq1075 X1 X1
       have r₂ := eq1021 X0 X1 X1
       grind)
    | exact resolve eq1075 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1075
  have eq49485 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49136 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49136
  have eq49512 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49485 X0 X1 X2
       have j1 := eq114 X1 X0
       grind)
    | (have r₁ := eq49485 X1 X0 X2
       have r₂ := eq114 X0 X1
       grind)
    | exact resolve eq49485 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq49485
  have eq228072 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq49512 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49512
  have eq228073 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq228072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228072
  have eq228075 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq228073 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq228073
    | exact resolve eq228073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228121 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq21343
       have i₂ := eq228073 x
       grind)
    | exact superpose eq228073 eq21343
    | exact resolve eq21343 eq228073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21343 eq228073
  have eq228351 : (σ (M.op x x)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq228121
       have i₂ := eq39541 x
       grind)
    | exact superpose eq39541 eq228121
    | exact resolve eq228121 eq39541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39541 eq228121
  have eq228371 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq228075 X0
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq228075
    | exact resolve eq228075 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq228075
  have eq228430 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq228371 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq228371
    | exact resolve eq228371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228371
  have eq229706 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq228351
       have i₂ := eq228430 x
       grind)
    | exact superpose eq228430 eq228351
    | exact resolve eq228351 eq228430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228351 eq228430
  have eq229727 : False := by grind
  exact eq229727

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation3735 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3735 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1) X1
       have i₂ := eq8 X1 X1 X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq8 X1 X1 X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq16
    | exact resolve eq16 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq45 X0 (τ X1) X2
       grind)
    | exact superpose eq45 eq16
    | (have j1 := eq45 (σ X0) X1 X2
       grind)
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq45 X0 (σ X1) X2
       grind)
    | exact superpose eq45 eq20
    | (have j1 := eq45 (τ X0) X1 X2
       grind)
    | exact resolve eq20 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq45 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq117
    | exact resolve eq117 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq287 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq130
    | exact resolve eq130 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 X1
       have i₂ := eq130 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq130 eq21
    | exact resolve eq21 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq130
  have eq339 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X0 X1 X2 X3
       have i₂ := eq306 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq306 eq287
    | exact resolve eq287 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq345 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq339 X0 X1 x X3
       have i₂ := eq306 X1 X3 x
       grind)
    | exact superpose eq306 eq339
    | exact resolve eq339 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) X2 (σ X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X1) X1
       have i₂ := eq43 X1 X1
       grind)
    | exact superpose eq43 eq32
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq32 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq406 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X0 X1 X2
       have i₂ := eq345 (σ (k X0 X1)) X2 (σ X0)
       grind)
    | exact superpose eq345 eq359
    | (have j0 := eq359 X0 X1 X2
       grind)
    | exact resolve eq359 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq448 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (M.op X0 X2) X1
       have i₂ := eq306 X0 X1 X2
       grind)
    | exact superpose eq306 eq72
    | (have j0 := eq72 (M.op X0 X2) X1
       grind)
    | (have r₁ := eq72 (M.op X0 X1) X1
       have r₂ := eq306 X0 X1 X1
       grind)
    | exact resolve eq72 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq454 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X0 X2) X1
       have i₂ := eq306 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq306 eq11
    | exact resolve eq11 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq454 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq454
    | (have j0 := eq454 X0 X1 X2
       grind)
    | (have r₁ := eq454 x x X2
       have r₂ := eq345 x x x
       grind)
    | exact resolve eq454 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq478 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq459 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq459
    | (have j0 := eq459 X0 X1 X2
       grind)
    | (have r₁ := eq459 (M.op X1 x) X1 X2
       have r₂ := eq345 (M.op X1 x) X1 x
       grind)
    | (have r₁ := eq459 X1 (M.op X1 x) X2
       have r₂ := eq345 X1 X1 x
       grind)
    | exact resolve eq459 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq1358 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k (τ (σ X0)) X2))) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 (σ X0) X2 X1
       have i₂ := eq62 X0 (σ X2) X3
       grind)
    | exact superpose eq62 eq18
    | (have j1 := eq62 X0 X1 X3
       grind)
    | exact resolve eq18 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq62
  have eq1381 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 X2))) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1358 X0 X1 X2 X3
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1358
    | (have j0 := eq1358 X0 X1 X2 X3
       grind)
    | exact resolve eq1358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1389 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 X2))) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1381 X0 X1 X2 X3
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1381
    | (have j0 := eq1381 X0 X1 X2 X3
       grind)
    | exact resolve eq1381 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1684 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 (σ X0) X1 X2
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1777 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | (have j0 := eq41 X1 X1
       grind)
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1880 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1777 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1777
    | (have j0 := eq1777 X0 X1
       grind)
    | exact resolve eq1777 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq2725 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 X1
       have i₂ := eq1880 X0 X1
       grind)
    | exact superpose eq1880 eq34
    | (have j1 := eq1880 X2 X0
       grind)
    | exact resolve eq34 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1880
  have eq3567 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3586 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3567 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3567
    | (have j0 := eq3567 X0
       grind)
    | exact resolve eq3567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq3596 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3586 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3586
    | (have j0 := eq3586 X0
       grind)
    | exact resolve eq3586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq4223 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq70 x y X0
       grind)
    | exact superpose eq70 eq14
    | (have j1 := eq70 x x X0
       grind)
    | exact resolve eq14 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq4325 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq4223 X0
       have j1 := eq2725 x X0 x
       grind)
    | (have r₁ := eq4223 X0
       have r₂ := eq2725 x x y
       grind)
    | exact resolve eq4223 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725 eq4223
  have eq4376 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3596 (σ x)
       have i₂ := eq4325 (σ x)
       grind)
    | exact superpose eq4325 eq3596
    | (have j0 := eq3596 (σ x)
       grind)
    | (have r₁ := eq3596 (σ x)
       have r₂ := eq4325 (σ x)
       grind)
    | exact resolve eq3596 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4392 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) X0
       have i₂ := eq4325 (σ X0)
       grind)
    | exact superpose eq4325 eq20
    | exact resolve eq20 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325
  have eq4395 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4376
  have eq4396 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq4392 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4392
    | exact resolve eq4392 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4537 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3596 x
       have i₂ := eq4396 x
       grind)
    | exact superpose eq4396 eq3596
    | (have j0 := eq3596 x
       grind)
    | (have r₁ := eq3596 x
       have r₂ := eq4396 x
       grind)
    | exact resolve eq3596 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq4556 : x = (M.op x x) := by grind
  clear eq4537
  have eq9389 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq373 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq373
    | (have j0 := eq373 (τ X0) X1
       grind)
    | exact resolve eq373 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq9456 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9389 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9389
    | (have j0 := eq9389 X0 X1
       grind)
    | exact resolve eq9389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9389
  have eq9469 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9456 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9456
    | (have j0 := eq9456 X0 X1
       grind)
    | exact resolve eq9456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9456
  have eq9589 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq406
    | (have j0 := eq406 (τ X0) X1 X2
       grind)
    | exact resolve eq406 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq9833 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9589 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9589
    | (have j0 := eq9589 X0 X1 X2
       grind)
    | exact resolve eq9589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9589
  have eq9877 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9833 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9833
    | (have j0 := eq9833 X0 X1 X2
       grind)
    | exact resolve eq9833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9833
  have eq9896 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9877 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9877
    | (have j0 := eq9877 X0 X1 X2
       grind)
    | exact resolve eq9877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9877
  have eq19708 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3596 (k X0 X0)
       have i₂ := eq9469 X0 (k X0 X0)
       grind)
    | exact superpose eq9469 eq3596
    | (have j0 := eq3596 (k X0 X0)
       have j1 := eq9469 (k X0 X0) x
       grind)
    | (have r₁ := eq3596 (k X0 X0)
       have r₂ := eq9469 X0 (k X0 X0)
       grind)
    | exact resolve eq3596 eq9469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596 eq9469
  have eq19733 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19708
  have eq69687 : ∀ X0 X1 X2 X3 : G, (τ (σ (k X0 X1))) = (k X0 (k X1 X2)) ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (k X0 (k X1 X2))
       have i₂ := eq1389 X1 X0 X2 X3
       grind)
    | exact superpose eq1389 eq9
    | (have j1 := eq1389 X1 X1 X2 X3
       grind)
    | exact resolve eq9 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq69905 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X0 (k X1 X2)) ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69687 X0 X1 X2 X3
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq69687
    | (have j0 := eq69687 X0 X1 X2 X3
       grind)
    | exact resolve eq69687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69687
  have eq82293 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq83509 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 (σ X1)) X1
       have i₂ := eq82293 X0 (σ X1)
       grind)
    | exact superpose eq82293 eq20
    | exact resolve eq20 eq82293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111405 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9896 X0 X0 (k X0 X0)
       have i₂ := eq19733 X0
       grind)
    | exact superpose eq19733 eq9896
    | (have j0 := eq9896 X0 x x
       have j1 := eq19733 X0
       grind)
    | exact resolve eq9896 eq19733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9896 eq19733
  have eq111537 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq111405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111405
  have eq112866 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 (k X0 X0) x
       have i₂ := eq111537 X0
       grind)
    | exact superpose eq111537 eq478
    | (have j1 := eq111537 X0
       grind)
    | exact resolve eq478 eq111537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq113074 : ∀ X0 X1 : G, (M.op X0 X0) = (k (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq112866 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq112866 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq112866 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112866
  have eq115641 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113074 X0 X1
       have i₂ := eq45 X0 X0 X2
       grind)
    | exact superpose eq45 eq113074
    | (have j0 := eq113074 X0 X1
       have j1 := eq45 X0 X1 X2
       grind)
    | exact resolve eq113074 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113074
  have eq116081 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq115641 X0 X1 X2
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq115641 X0 X1 X2
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq115641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115641
  have eq118707 : ∀ X0 X1 X2 X3 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (k X0 X2) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq116081 X0 X1 X2
       grind)
    | exact superpose eq116081 eq11
    | (have j1 := eq116081 X0 X1 X3
       grind)
    | exact resolve eq11 eq116081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119492 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116081 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116081
  have eq119688 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X0 X2) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq118707 X0 X1 X2 X3
       have j1 := eq45 X0 X1 X3
       grind)
    | (have r₁ := eq118707 X0 X1 X2 X3
       have r₂ := eq45 X0 X1 X2
       grind)
    | exact resolve eq118707 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq118707
  have eq120977 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119492 X0 (k X0 X0)
       have i₂ := eq111537 X0
       grind)
    | exact superpose eq111537 eq119492
    | (have j1 := eq111537 X0
       grind)
    | exact resolve eq119492 eq111537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111537
  have eq121151 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq119492 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119492
  have eq121265 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq120977 X0
       have j1 := eq69905 X0 X0 X0 x
       grind)
    | (have r₁ := eq120977 x
       have r₂ := eq69905 X0 x x x
       grind)
    | exact resolve eq120977 eq69905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69905 eq120977
  have eq121316 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq121265 X0
       have i₂ := eq121151 X0
       grind)
    | exact superpose eq121151 eq121265
    | (have j0 := eq121265 X0
       grind)
    | exact resolve eq121265 eq121151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121265
  have eq121362 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq121316 X0
       have j1 := eq11 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq121316 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq121316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121316
  have eq122563 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq121151 (σ X0)
       grind)
    | exact superpose eq121151 eq13
    | exact resolve eq13 eq121151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122594 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq121151 (τ X0)
       grind)
    | exact superpose eq121151 eq46
    | exact resolve eq46 eq121151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq122673 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122594 X0
       have i₂ := eq121151 X0
       grind)
    | exact superpose eq121151 eq122594
    | exact resolve eq122594 eq121151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122594
  have eq122680 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq122563 X0
       have i₂ := eq121151 X0
       grind)
    | exact superpose eq121151 eq122563
    | exact resolve eq122563 eq121151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121151 eq122563
  have eq123992 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121362 (M.op X0 x)
       have i₂ := eq306 X0 (M.op X0 x) x
       grind)
    | exact superpose eq306 eq121362
    | exact resolve eq121362 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121362
  have eq124426 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123992 X1 x
       have i₂ := eq345 X1 X1 x
       grind)
    | exact superpose eq345 eq123992
    | exact resolve eq123992 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123992
  have eq125825 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (τ X0) X1 (τ X0)
       have i₂ := eq122673 X0
       grind)
    | exact superpose eq122673 eq306
    | exact resolve eq306 eq122673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125835 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X1 (τ X0) (τ X0)
       have i₂ := eq122673 X0
       grind)
    | exact superpose eq122673 eq345
    | exact resolve eq345 eq122673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122673
  have eq127431 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (σ X0) X1 (σ X0)
       have i₂ := eq122680 X0
       grind)
    | exact superpose eq122680 eq306
    | exact resolve eq306 eq122680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122680
  have eq128955 : ∀ X0 : G, (σ x) = (k (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq124426 (σ x) x
       have i₂ := eq4395
       grind)
    | exact superpose eq4395 eq124426
    | exact resolve eq124426 eq4395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq128979 : ∀ X0 : G, x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq124426 x x
       have i₂ := eq4556
       grind)
    | exact superpose eq4556 eq124426
    | exact resolve eq124426 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124426
  have eq131594 : ∀ X0 : G, (τ (σ x)) = (k (τ (M.op (σ x) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (σ x) X0) x
       have i₂ := eq128955 X0
       grind)
    | exact superpose eq128955 eq20
    | exact resolve eq20 eq128955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq128955
  have eq131647 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) x) := by
    intro X0
    first
    | (have i₁ := eq131594 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq131594
    | exact resolve eq131594 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131594
  have eq136275 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (τ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125825 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq125825
    | exact resolve eq125825 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136876 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136275 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq136275
    | exact resolve eq136275 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136275
  have eq137030 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136876 X0 X1 X2
       have i₂ := eq125825 X0 X2
       grind)
    | exact superpose eq125825 eq136876
    | exact resolve eq136876 eq125825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125825 eq136876
  have eq137934 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125835 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq125835
    | exact resolve eq125835 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138519 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X0))) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137934 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq137934
    | exact resolve eq137934 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137934
  have eq138607 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138519 X0 X1 X2
       have i₂ := eq125835 X0 X2
       grind)
    | exact superpose eq125835 eq138519
    | exact resolve eq138519 eq125835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125835 eq138519
  have eq139451 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127431 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq127431
    | exact resolve eq127431 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140114 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139451 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq139451
    | exact resolve eq139451 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139451
  have eq140265 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140114 X0 X1 X2
       have i₂ := eq127431 X0 X2
       grind)
    | exact superpose eq127431 eq140114
    | exact resolve eq140114 eq127431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127431 eq140114
  have eq145967 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (M.op X0 (τ X1)) (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82293 X2 (τ (M.op X0 X1))
       have i₂ := eq138607 X0 X1 X2
       grind)
    | exact superpose eq138607 eq82293
    | exact resolve eq82293 eq138607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82293 eq138607
  have eq185195 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X0 X2) ∨ (k X0 X1) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq119688 X0 X1 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119688
  have eq189223 : ∀ X0 X1 : G, x ≠ (M.op (M.op x X0) X1) ∨ x = (k (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq185195 (M.op x X0) X1 x
       have i₂ := eq128979 X0
       grind)
    | exact superpose eq128979 eq185195
    | exact resolve eq185195 eq128979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128979
  have eq189333 : ∀ X0 X1 : G, x ≠ (M.op (τ (M.op (σ x) X0)) X1) ∨ x = (k (τ (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq185195 (τ (M.op (σ x) X0)) X1 x
       have i₂ := eq131647 X0
       grind)
    | exact superpose eq131647 eq185195
    | exact resolve eq185195 eq131647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131647 eq185195
  have eq189354 : ∀ X0 X1 : G, x ≠ (M.op (τ (σ x)) X1) ∨ x = (k (τ (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq189333 X0 X1
       have i₂ := eq137030 (σ x) X0 X1
       grind)
    | exact superpose eq137030 eq189333
    | (have j0 := eq189333 X0 X1
       grind)
    | exact resolve eq189333 eq137030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137030 eq189333
  have eq189373 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq189223 X0 X1
       have i₂ := eq306 x X1 X0
       grind)
    | exact superpose eq306 eq189223
    | (have j0 := eq189223 X0 X1
       grind)
    | exact resolve eq189223 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq189223
  have eq189500 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k (τ (M.op (σ x) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq189354 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq189354
    | (have j0 := eq189354 X0 X1
       grind)
    | exact resolve eq189354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189354
  have eq190959 : ∀ X0 X1 X2 : G, x ≠ (M.op x X0) ∨ x = (k (M.op x X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189373 X2 (M.op X0 X1)
       have i₂ := eq345 x X0 X1
       grind)
    | exact superpose eq345 eq189373
    | (have j0 := eq189373 X0 X0
       grind)
    | exact resolve eq189373 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189373
  have eq221952 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X0) (τ (M.op (σ X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145967 X0 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq145967
    | exact resolve eq145967 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145967
  have eq223584 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (σ X1) X2) (M.op X0 X1)
       have i₂ := eq221952 X1 X0 X2
       grind)
    | exact superpose eq221952 eq16
    | exact resolve eq16 eq221952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq221952
  have eq228328 : ∀ X0 X1 : G, x ≠ x ∨ x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq190959 x X1 X0
       have i₂ := eq4556
       grind)
    | exact superpose eq4556 eq190959
    | (have j0 := eq190959 x X1 X0
       grind)
    | (have r₁ := eq190959 x X1 x
       have r₂ := eq4556
       grind)
    | exact resolve eq190959 eq4556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556 eq190959
  have eq228351 : ∀ X0 X1 : G, x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq228328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228328
  have eq229304 : ∀ X0 X2 : G, x = (M.op x X0) ∨ (k (σ (M.op x X0)) X2) = (M.op (σ (M.op x X0)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq1684 (M.op x X0) (M.op x x) X2
       have i₂ := eq228351 X0 x
       grind)
    | exact superpose eq228351 eq1684
    | (have j0 := eq1684 (M.op x X0) x X2
       grind)
    | exact resolve eq1684 eq228351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq228351
  have eq229417 : ∀ X0 X2 : G, (M.op (σ x) X2) = (k (σ (M.op x X0)) X2) ∨ x = (M.op x X0) := by
    intro X0 X2
    first
    | (have i₁ := eq229304 X0 X2
       have i₂ := eq140265 x X0 X2
       grind)
    | exact superpose eq140265 eq229304
    | (have j0 := eq229304 X0 X2
       grind)
    | exact resolve eq229304 eq140265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140265 eq229304
  have eq844201 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op (σ x) (M.op (σ X0) X1)) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq223584 x X0 X1
       have i₂ := eq229417 X0 (M.op (σ X0) X1)
       grind)
    | exact superpose eq229417 eq223584
    | (have j1 := eq229417 X0 x
       grind)
    | exact resolve eq223584 eq229417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223584 eq229417
  have eq844218 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq844201 X0 x
       have i₂ := eq345 (σ x) (σ X0) x
       grind)
    | exact superpose eq345 eq844201
    | (have j0 := eq844201 X0 x
       grind)
    | exact resolve eq844201 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq844201
  have eq847469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq844218 y
       grind)
    | exact superpose eq844218 eq14
    | (have j1 := eq844218 y
       grind)
    | (have r₁ := eq14
       have r₂ := eq844218 y
       grind)
    | exact resolve eq14 eq844218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844218
  have eq847545 : x = (M.op x y) := by grind
  clear eq847469
  have eq850517 : ∀ X0 : G, x ≠ x ∨ x = (k (τ (M.op (σ x) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq189500 X0 y
       have i₂ := eq847545
       grind)
    | exact superpose eq847545 eq189500
    | (have j0 := eq189500 X0 y
       grind)
    | (have r₁ := eq189500 X0 y
       have r₂ := eq847545
       grind)
    | exact resolve eq189500 eq847545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189500
  have eq850694 : ∀ X0 : G, x = (k (τ (M.op (σ x) X0)) y) := by
    intro X0
    first
    | (have j0 := eq850517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850517
  have eq871929 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq83509 (σ x) y
       have i₂ := eq850694 (σ y)
       grind)
    | exact superpose eq850694 eq83509
    | exact resolve eq83509 eq850694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83509 eq850694
  have eq875140 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq871929
       grind)
    | exact superpose eq871929 eq10
    | exact resolve eq10 eq871929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871929
  have eq878929 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq875140
       grind)
    | exact superpose eq875140 eq14
    | exact resolve eq14 eq875140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875140
  have eq879153 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq878929
       have i₂ := eq847545
       grind)
    | exact superpose eq847545 eq878929
    | exact resolve eq878929 eq847545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847545 eq878929
  have eq879154 : False := by grind
  exact eq879154

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3735 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op (M.op X1 X0) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X0) (M.op X0 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq12 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq12 X0 (M.op (M.op X0 x) (M.op X1 X0))
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq30 (τ X0) X1
       grind)
    | exact superpose eq30 eq17
    | (have j1 := eq30 (τ X0) X1
       grind)
    | exact resolve eq17 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq100 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq42
  have eq114 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq100
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq126 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq126
    | exact resolve eq126 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq146 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op X3 (M.op X0 X1)) ∨ (M.op X3 (M.op X1 X0)) = (k (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X3 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq32
    | (have j0 := eq32 X3 (M.op X1 X0) X2
       grind)
    | exact resolve eq32 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq166 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X1 X0)) = (k (M.op X1 X0) X3) ∨ (M.op X1 X0) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq146 X0 X1 x X3
       have i₂ := eq140 X0 X1 x
       grind)
    | exact superpose eq140 eq146
    | (have j0 := eq146 X0 X1 x X3
       grind)
    | exact resolve eq146 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq259 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X1 X2)) ∨ (M.op (M.op X1 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 X0) (M.op X0 X1) x
       have i₂ := eq19 X1 X0 X2 x
       grind)
    | exact superpose eq19 eq31
    | (have j0 := eq31 (M.op X1 X0) (M.op X0 X1) X2
       grind)
    | exact resolve eq31 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq31
  have eq273 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op (M.op X1 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1 x
       have i₂ := eq140 X1 X0 x
       grind)
    | exact superpose eq140 eq259
    | (have j0 := eq259 X0 X1 x
       grind)
    | exact resolve eq259 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq298 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 X1) (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq8 X1 X0 X0
       grind)
    | exact superpose eq8 eq273
    | (have j0 := eq273 X0 X1
       grind)
    | exact resolve eq273 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq311 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq140 X0 X1 X2
       grind)
    | exact superpose eq140 eq140
    | exact resolve eq140 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq140 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq140
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1 X2 X1
       have i₂ := eq140 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq140 eq18
    | exact resolve eq18 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq366 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq311 X0 X1 X2 X3
       have i₂ := eq331 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq331 eq311
    | exact resolve eq311 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq372 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq366 X0 X1 x X3
       have i₂ := eq331 X1 X3 x
       grind)
    | exact superpose eq331 eq366
    | exact resolve eq366 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq435 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq445 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 (M.op X0 X2)
       have i₂ := eq331 X0 X1 X2
       grind)
    | exact superpose eq331 eq67
    | (have j0 := eq67 X1 X0
       grind)
    | exact resolve eq67 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq372 X0 X0 X1
       grind)
    | exact superpose eq372 eq435
    | exact resolve eq435 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq493 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 (σ X1) X2 (σ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq140
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq140 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq33
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq33 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq548 : ∀ X0 X1 X2 : G, (M.op X1 (σ X2)) = (M.op (M.op X1 (σ X2)) (σ X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 (σ X2) X1 (σ X2)
       have i₂ := eq34 X0 X2
       grind)
    | exact superpose eq34 eq140
    | (have j1 := eq34 X0 X2
       grind)
    | exact resolve eq140 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq140
  have eq553 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq548 X0 X1 X2
       have i₂ := eq331 X1 (σ X0) (σ X2)
       grind)
    | exact superpose eq331 eq548
    | (have j0 := eq548 X0 X1 X2
       grind)
    | exact resolve eq548 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq570 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq520 X0 X1 X2
       have i₂ := eq331 X2 (σ (k X0 X1)) (σ X1)
       grind)
    | exact superpose eq331 eq520
    | (have j0 := eq520 X0 X1 X2
       grind)
    | exact resolve eq520 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq2968 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq3141 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2968 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2968
    | (have j0 := eq2968 X0 X1
       grind)
    | exact resolve eq2968 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq3256 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1 x
       have i₂ := eq315 X0 X1 x
       grind)
    | exact superpose eq315 eq372
    | (have j1 := eq315 X0 X1 x
       grind)
    | exact resolve eq372 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq372
  have eq3389 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq3438 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3389 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3389
    | (have j0 := eq3389 X0 X1
       grind)
    | exact resolve eq3389 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq3972 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60 y x
       grind)
    | exact superpose eq60 eq14
    | (have j1 := eq60 y x
       grind)
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq5965 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X1 X1
       have i₂ := eq3141 X0 X1
       grind)
    | (have i₁ := eq456 X0 X1
       have i₂ := eq3141 (M.op X0 X1) X1
       grind)
    | exact superpose eq3141 eq456
    | (have j1 := eq3141 X0 X1
       grind)
    | exact resolve eq456 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22526 : ∀ X0 X1 X2 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq493 X1 X0
       have i₂ := eq5965 X0 X2
       grind)
    | exact superpose eq5965 eq493
    | (have j0 := eq493 X1 X0
       have j1 := eq5965 X0 X2
       grind)
    | exact resolve eq493 eq5965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq5965
  have eq22610 : ∀ X0 X1 X2 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq22526 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22526
  have eq55675 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq534 x X0 y
       grind)
    | exact superpose eq534 eq14
    | (have j1 := eq534 x X0 x
       grind)
    | (have r₁ := eq14
       have r₂ := eq534 (M.op x y) (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq14 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq55920 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have j0 := eq55675 X0
       have j1 := eq22610 x X0 x
       grind)
    | (have r₁ := eq55675 X0
       have r₂ := eq22610 (M.op x y) (σ (k y x)) x
       grind)
    | (have r₁ := eq55675 X0
       have r₂ := eq22610 (k y x) (σ (M.op x y)) x
       grind)
    | (have r₁ := eq55675 X0
       have r₂ := eq22610 x x y
       grind)
    | exact resolve eq55675 eq22610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22610 eq55675
  have eq56058 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq55920
  have eq56112 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56058
       have i₂ := eq331 (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq331 eq56058
    | exact resolve eq56058 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56058
  have eq56113 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq56112
  have eq58455 : x = (k x (τ (σ x))) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq56113
       grind)
    | exact superpose eq56113 eq114
    | exact resolve eq114 eq56113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq58609 : x = (k x x) := by
    first
    | (have i₁ := eq58455
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq58455
    | exact resolve eq58455 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58455
  have eq62064 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3256 x x
       have i₂ := eq58609
       grind)
    | exact superpose eq58609 eq3256
    | (have j0 := eq3256 x x
       grind)
    | exact resolve eq3256 eq58609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58609
  have eq62069 : x = (M.op x x) := by grind
  clear eq62064
  have eq65955 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq456 x X0
       have i₂ := eq62069
       grind)
    | exact superpose eq62069 eq456
    | exact resolve eq456 eq62069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq66006 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq166 x x x
       have i₂ := eq62069
       grind)
    | exact superpose eq62069 eq166
    | exact resolve eq166 eq62069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq66034 : ∀ X0 : G, x ≠ x ∨ x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq445 x x X0
       have i₂ := eq62069
       grind)
    | exact superpose eq62069 eq445
    | (have j0 := eq445 x x X0
       grind)
    | (have r₁ := eq445 x x x
       have r₂ := eq62069
       grind)
    | exact resolve eq445 eq62069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq62069
  have eq66047 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq66034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66034
  have eq158410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3972
       have i₂ := eq3141 x y
       grind)
    | exact superpose eq3141 eq3972
    | (have j1 := eq3141 x y
       grind)
    | (have r₁ := eq3972
       have r₂ := eq3141 x y
       grind)
    | exact resolve eq3972 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq158411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq3972
       have i₂ := eq3438 x y
       grind)
    | exact superpose eq3438 eq3972
    | (have j1 := eq3438 x y
       grind)
    | (have r₁ := eq3972
       have r₂ := eq3438 x y
       grind)
    | exact resolve eq3972 eq3438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438 eq3972
  have eq158420 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq158411
  have eq158421 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq158410
  have eq158432 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq158420
       grind)
    | exact superpose eq158420 eq9
    | exact resolve eq9 eq158420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158420
  have eq158477 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq158432
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq158432
    | exact resolve eq158432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158432
  have eq158478 : y = (k y x) := by
    first
    | (have j1 := eq67 y x
       grind)
    | (have r₁ := eq158477
       have r₂ := eq67 y x
       grind)
    | exact resolve eq158477 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158477
  have eq158565 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3256 x y
       have i₂ := eq158478
       grind)
    | exact superpose eq158478 eq3256
    | (have j0 := eq3256 x y
       grind)
    | exact resolve eq3256 eq158478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq159659 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66047 y
       have i₂ := eq158565
       grind)
    | exact superpose eq158565 eq66047
    | exact resolve eq66047 eq158565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66047 eq158565
  have eq160431 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66006 y
       have i₂ := eq159659
       grind)
    | exact superpose eq159659 eq66006
    | (have j0 := eq66006 y
       grind)
    | exact resolve eq66006 eq159659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66006 eq159659
  have eq160454 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq160431
  have eq160748 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq298 x y
       have i₂ := eq160454
       grind)
    | exact superpose eq160454 eq298
    | exact resolve eq298 eq160454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq160454
  have eq160773 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq160748
  have eq160779 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160773
       have i₂ := eq65955 y
       grind)
    | exact superpose eq65955 eq160773
    | exact resolve eq160773 eq65955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65955 eq160773
  have eq160780 : x = (M.op x y) := by grind
  clear eq160779
  have eq161747 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq158421
       have i₂ := eq160780
       grind)
    | exact superpose eq160780 eq158421
    | exact resolve eq158421 eq160780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158421
  have eq161931 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq161747
       grind)
    | exact superpose eq161747 eq8
    | exact resolve eq8 eq161747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161747
  have eq162060 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq161931 x
       have i₂ := eq331 y x x
       grind)
    | exact superpose eq331 eq161931
    | exact resolve eq161931 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq161931
  have eq162192 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 x y
       have i₂ := eq162060
       grind)
    | exact superpose eq162060 eq67
    | (have j0 := eq67 x y
       grind)
    | (have r₁ := eq67 x y
       have r₂ := eq162060
       grind)
    | exact resolve eq67 eq162060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq162060
  have eq162274 : x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq162192
  have eq167364 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq553 x X0 y
       grind)
    | exact superpose eq553 eq14
    | (have j1 := eq553 y X0 x
       grind)
    | exact resolve eq14 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq167395 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq167364 X0
       have i₂ := eq158478
       grind)
    | exact superpose eq158478 eq167364
    | (have j0 := eq167364 X0
       grind)
    | exact resolve eq167364 eq158478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158478 eq167364
  have eq167419 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq167395 X0
       have i₂ := eq160780
       grind)
    | exact superpose eq160780 eq167395
    | (have j0 := eq167395 X0
       grind)
    | exact resolve eq167395 eq160780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167395
  have eq167749 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq570 x y X0
       have i₂ := eq162274
       grind)
    | exact superpose eq162274 eq570
    | (have j0 := eq570 x y x
       grind)
    | exact resolve eq570 eq162274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq162274
  have eq167864 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq167749 X0
       have j1 := eq167419 X0
       grind)
    | (have r₁ := eq167749 X0
       have r₂ := eq167419 X0
       grind)
    | exact resolve eq167749 eq167419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167749
  have eq167873 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq167864 X0
       have i₂ := eq56113
       grind)
    | exact superpose eq56113 eq167864
    | (have j0 := eq167864 X0
       grind)
    | exact resolve eq167864 eq56113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167864
  have eq167876 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq167873 X0
       have j1 := eq167419 X0
       grind)
    | (have r₁ := eq167873 X0
       have r₂ := eq167419 X0
       grind)
    | exact resolve eq167873 eq167419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167419 eq167873
  have eq168108 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq167876 (σ x)
       grind)
    | exact superpose eq167876 eq14
    | exact resolve eq14 eq167876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167876
  have eq168155 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq168108
       have i₂ := eq56113
       grind)
    | exact superpose eq56113 eq168108
    | exact resolve eq168108 eq56113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56113 eq168108
  have eq168237 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq168155
       have i₂ := eq160780
       grind)
    | exact superpose eq160780 eq168155
    | exact resolve eq168155 eq160780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160780 eq168155
  have eq168238 : False := by grind
  exact eq168238

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pyx_Equation3735 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3735 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X3 (M.op X1 X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq8 X1 X1 X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq8 X1 X1 X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
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
  have eq45 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq66 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq45 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq45 eq13
    | (have j1 := eq45 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq45 X0 (σ X1) X2
       grind)
    | exact superpose eq45 eq28
    | (have j1 := eq45 (τ X0) X1 X2
       grind)
    | exact resolve eq28 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X1 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X1 X3 X0 (M.op X0 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X1 X2 x
       have i₂ := eq8 X1 X0 x
       grind)
    | exact superpose eq8 eq117
    | exact resolve eq117 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq287 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq130 (M.op X0 X2) (M.op X1 X0) X2
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq130
    | exact resolve eq130 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X2 X1
       have i₂ := eq130 X1 X0 (M.op X0 X2)
       grind)
    | exact superpose eq130 eq21
    | exact resolve eq21 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq130
  have eq339 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X0 X1 X2 X3
       have i₂ := eq306 X0 (M.op (M.op X1 X2) X3) X1
       grind)
    | exact superpose eq306 eq287
    | exact resolve eq287 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq345 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq339 X0 X1 x X3
       have i₂ := eq306 X1 X3 x
       grind)
    | exact superpose eq306 eq339
    | exact resolve eq339 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq359 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) (M.op X2 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) X2 (σ X0)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq8
    | (have j1 := eq41 X1 X1
       grind)
    | exact resolve eq8 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X1) X1
       have i₂ := eq41 X1 X1
       grind)
    | exact superpose eq41 eq32
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq32 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq406 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X0 X1 X2
       have i₂ := eq345 (σ (k X0 X1)) X2 (σ X1)
       grind)
    | exact superpose eq345 eq359
    | (have j0 := eq359 X0 X1 X2
       grind)
    | exact resolve eq359 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq448 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 (M.op X0 X2)
       have i₂ := eq306 X0 X1 X2
       grind)
    | exact superpose eq306 eq71
    | (have j0 := eq71 X1 (M.op X0 X2)
       grind)
    | (have r₁ := eq71 X1 (M.op X0 X1)
       have r₂ := eq306 X0 X1 X1
       grind)
    | exact resolve eq71 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq454 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X0 X2)
       have i₂ := eq306 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq306 eq11
    | exact resolve eq11 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq454 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq454
    | (have j0 := eq454 X0 X1 X2
       grind)
    | (have r₁ := eq454 x x X2
       have r₂ := eq345 x x x
       grind)
    | exact resolve eq454 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq478 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq459 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq459
    | (have j0 := eq459 X0 X1 X2
       grind)
    | (have r₁ := eq459 (M.op X1 x) X1 X2
       have r₂ := eq345 (M.op X1 x) X1 x
       grind)
    | (have r₁ := eq459 X1 (M.op X1 x) X2
       have r₂ := eq345 X1 X1 x
       grind)
    | exact resolve eq459 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq1685 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 (σ X0) X1 X2
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1778 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | (have j0 := eq42 X1 X1
       grind)
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1881 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1778 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1778
    | (have j0 := eq1778 X0 X1
       grind)
    | exact resolve eq1778 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq2725 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 X1
       have i₂ := eq1881 X0 X1
       grind)
    | exact superpose eq1881 eq34
    | (have j1 := eq1881 X2 X0
       grind)
    | exact resolve eq34 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1881
  have eq3568 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3587 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3568 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3568
    | (have j0 := eq3568 X0
       grind)
    | exact resolve eq3568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq3597 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3587 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3587
    | (have j0 := eq3587 X0
       grind)
    | exact resolve eq3587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq4224 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq66 x y X0
       grind)
    | exact superpose eq66 eq14
    | (have j1 := eq66 x x X0
       grind)
    | exact resolve eq14 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq4326 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4224 X0
       have j1 := eq2725 x X0 x
       grind)
    | (have r₁ := eq4224 X0
       have r₂ := eq2725 x x y
       grind)
    | exact resolve eq4224 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725 eq4224
  have eq4374 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3597 (σ x)
       have i₂ := eq4326 (σ x)
       grind)
    | exact superpose eq4326 eq3597
    | (have j0 := eq3597 (σ x)
       grind)
    | (have r₁ := eq3597 (σ x)
       have r₂ := eq4326 (σ x)
       grind)
    | exact resolve eq3597 eq4326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4391 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq4326 (σ X0)
       grind)
    | exact superpose eq4326 eq28
    | exact resolve eq28 eq4326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4326
  have eq4396 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4374
  have eq4397 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4391 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4391
    | exact resolve eq4391 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391
  have eq4538 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3597 x
       have i₂ := eq4397 x
       grind)
    | exact superpose eq4397 eq3597
    | (have j0 := eq3597 x
       grind)
    | (have r₁ := eq3597 x
       have r₂ := eq4397 x
       grind)
    | exact resolve eq3597 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397
  have eq4557 : x = (M.op x x) := by grind
  clear eq4538
  have eq9381 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (k X1 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq373 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq373
    | (have j0 := eq373 (τ X0) X1
       grind)
    | exact resolve eq373 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq373
  have eq9449 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9381 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9381
    | (have j0 := eq9381 X0 X1
       grind)
    | exact resolve eq9381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9462 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9449 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9449
    | (have j0 := eq9449 X0 X1
       grind)
    | exact resolve eq9449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq9573 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (σ (τ (k X0 X1))) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq406 (τ X0) (τ X1) X2
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq406
    | (have j0 := eq406 X0 (τ X1) X2
       grind)
    | exact resolve eq406 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq9813 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9573 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9573
    | (have j0 := eq9573 X0 X1 X2
       grind)
    | exact resolve eq9573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9573
  have eq9857 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9813 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9813
    | (have j0 := eq9813 X0 X1 X2
       grind)
    | exact resolve eq9813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9813
  have eq9878 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9857 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9857
    | (have j0 := eq9857 X0 X1 X2
       grind)
    | exact resolve eq9857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9857
  have eq19684 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3597 (k X0 X0)
       have i₂ := eq9462 X0 (k X0 X0)
       grind)
    | exact superpose eq9462 eq3597
    | (have j0 := eq3597 (k X0 X0)
       have j1 := eq9462 (k X0 X0) x
       grind)
    | (have r₁ := eq3597 (k X0 X0)
       have r₂ := eq9462 X0 (k X0 X0)
       grind)
    | exact resolve eq3597 eq9462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597 eq9462
  have eq19711 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq81353 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq82715 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k X1 (τ (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 (σ X1))
       have i₂ := eq81353 X0 (σ X1)
       grind)
    | exact superpose eq81353 eq28
    | exact resolve eq28 eq81353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109652 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9878 X0 X0 (k X0 X0)
       have i₂ := eq19711 X0
       grind)
    | exact superpose eq19711 eq9878
    | (have j0 := eq9878 X0 X0 x
       have j1 := eq19711 X0
       grind)
    | exact resolve eq9878 eq19711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9878 eq19711
  have eq109784 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq109652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109652
  have eq111037 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 (k X0 X0) x
       have i₂ := eq109784 X0
       grind)
    | exact superpose eq109784 eq478
    | (have j1 := eq109784 X0
       grind)
    | exact resolve eq478 eq109784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq111243 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq111037 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq111037 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq111037 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111037
  have eq114162 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111243 X0 X1
       have i₂ := eq45 X0 X0 X2
       grind)
    | exact superpose eq45 eq111243
    | (have j0 := eq111243 X0 X1
       have j1 := eq45 X0 X1 X2
       grind)
    | exact resolve eq111243 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111243
  have eq114612 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq114162 X0 X1 X2
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq114162 X1 X1 X2
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq114162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114162
  have eq117431 : ∀ X0 X1 X2 X3 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq114612 X0 X1 X2
       grind)
    | exact superpose eq114612 eq11
    | (have j1 := eq114612 X1 X1 X3
       grind)
    | exact resolve eq11 eq114612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117938 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114612 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114612
  have eq118107 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq117431 X0 X1 X2 X3
       have j1 := eq45 X1 X1 X3
       grind)
    | (have r₁ := eq117431 X1 X0 X2 X3
       have r₂ := eq45 X0 X1 X2
       grind)
    | exact resolve eq117431 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq117431
  have eq119552 : ∀ X0 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117938 (k X0 X0) X0
       have i₂ := eq109784 X0
       grind)
    | exact superpose eq109784 eq117938
    | (have j1 := eq109784 X0
       grind)
    | exact resolve eq117938 eq109784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109784
  have eq119722 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq117938 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117938
  have eq119834 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq119552 X0
       have j1 := eq118107 X0 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq119552 x
       have r₂ := eq118107 X0 x x x
       grind)
    | exact resolve eq119552 eq118107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119552
  have eq119885 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq119834 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq119834
    | (have j0 := eq119834 X0
       grind)
    | exact resolve eq119834 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119834
  have eq119931 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq119885 X0
       have j1 := eq11 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq119885 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq119885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119885
  have eq121408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq119722 (σ X0)
       grind)
    | exact superpose eq119722 eq13
    | exact resolve eq13 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121418 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq119722 (τ X0)
       grind)
    | exact superpose eq119722 eq46
    | exact resolve eq46 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq121474 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq121418 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq121418
    | exact resolve eq121418 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121418
  have eq121480 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq121408 X0
       have i₂ := eq119722 X0
       grind)
    | exact superpose eq119722 eq121408
    | exact resolve eq121408 eq119722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119722 eq121408
  have eq122658 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119931 (M.op X0 x)
       have i₂ := eq306 X0 (M.op X0 x) x
       grind)
    | exact superpose eq306 eq119931
    | exact resolve eq119931 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119931
  have eq123095 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122658 X1 x
       have i₂ := eq345 X1 X1 x
       grind)
    | exact superpose eq345 eq122658
    | exact resolve eq122658 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122658
  have eq124408 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (τ X0) X1 (τ X0)
       have i₂ := eq121474 X0
       grind)
    | exact superpose eq121474 eq306
    | exact resolve eq306 eq121474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124418 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X1 (τ X0) (τ X0)
       have i₂ := eq121474 X0
       grind)
    | exact superpose eq121474 eq345
    | exact resolve eq345 eq121474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121474
  have eq126139 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 (σ X0) X1 (σ X0)
       have i₂ := eq121480 X0
       grind)
    | exact superpose eq121480 eq306
    | exact resolve eq306 eq121480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121480
  have eq127721 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq123095 (σ x) x
       have i₂ := eq4396
       grind)
    | exact superpose eq4396 eq123095
    | exact resolve eq123095 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396
  have eq127744 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq123095 x x
       have i₂ := eq4557
       grind)
    | exact superpose eq4557 eq123095
    | exact resolve eq123095 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123095
  have eq130372 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op (σ x) X0)
       have i₂ := eq127721 X0
       grind)
    | exact superpose eq127721 eq28
    | exact resolve eq28 eq127721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq127721
  have eq130442 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq130372 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq130372
    | exact resolve eq130372 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130372
  have eq135278 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X1)) X2) = (M.op (τ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124408 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq124408
    | exact resolve eq124408 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135879 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135278 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq135278
    | exact resolve eq135278 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135278
  have eq136033 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq135879 X0 X1 X2
       have i₂ := eq124408 X0 X2
       grind)
    | exact superpose eq124408 eq135879
    | exact resolve eq135879 eq124408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124408 eq135879
  have eq137157 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124418 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq124418
    | exact resolve eq124418 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137740 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X0))) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137157 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq137157
    | exact resolve eq137157 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137157
  have eq137828 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137740 X0 X1 X2
       have i₂ := eq124418 X0 X2
       grind)
    | exact superpose eq124418 eq137740
    | exact resolve eq137740 eq124418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124418 eq137740
  have eq138898 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X1)) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126139 (M.op X0 X1) X2
       have i₂ := eq306 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq306 eq126139
    | exact resolve eq126139 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139561 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138898 X0 X1 X2
       have i₂ := eq345 X0 X0 X1
       grind)
    | exact superpose eq345 eq138898
    | exact resolve eq138898 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138898
  have eq139712 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139561 X0 X1 X2
       have i₂ := eq126139 X0 X2
       grind)
    | exact superpose eq126139 eq139561
    | exact resolve eq139561 eq126139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126139 eq139561
  have eq144824 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (τ (M.op X1 X2)) (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81353 X2 (τ (M.op X0 X1))
       have i₂ := eq137828 X0 X1 X2
       grind)
    | exact superpose eq137828 eq81353
    | exact resolve eq81353 eq137828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81353 eq137828
  have eq168773 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (k X2 X1) ∨ (k X0 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq118107 X0 X1 X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118107
  have eq170768 : ∀ X0 X1 : G, x ≠ (M.op (M.op x X0) X1) ∨ x = (k X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq168773 X0 (M.op x X0) x
       have i₂ := eq127744 X0
       grind)
    | exact superpose eq127744 eq168773
    | exact resolve eq168773 eq127744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127744
  have eq170773 : ∀ X0 X1 : G, x ≠ (M.op (τ (M.op (σ x) X0)) X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq168773 X0 (τ (M.op (σ x) X0)) x
       have i₂ := eq130442 X0
       grind)
    | exact superpose eq130442 eq168773
    | exact resolve eq168773 eq130442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130442 eq168773
  have eq170778 : ∀ X0 X1 : G, x ≠ (M.op (τ (σ x)) X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq170773 X0 X1
       have i₂ := eq136033 (σ x) X0 X1
       grind)
    | exact superpose eq136033 eq170773
    | (have j0 := eq170773 X0 X1
       grind)
    | exact resolve eq170773 eq136033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136033 eq170773
  have eq170781 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq170768 X0 X1
       have i₂ := eq306 x X1 X0
       grind)
    | exact superpose eq306 eq170768
    | (have j0 := eq170768 X0 X1
       grind)
    | exact resolve eq170768 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq170768
  have eq170840 : ∀ X0 X1 : G, x ≠ (M.op x X1) ∨ x = (k X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq170778 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq170778
    | (have j0 := eq170778 X0 X1
       grind)
    | exact resolve eq170778 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170778
  have eq171628 : ∀ X0 X1 X2 : G, x ≠ (M.op x X0) ∨ x = (k (M.op X0 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170781 X2 (M.op X0 X1)
       have i₂ := eq345 x X0 X1
       grind)
    | exact superpose eq345 eq170781
    | (have j0 := eq170781 X0 X0
       grind)
    | exact resolve eq170781 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170781
  have eq185234 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (τ (M.op (σ X0) X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144824 X0 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq144824
    | exact resolve eq144824 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144824
  have eq186138 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (M.op (σ X1) X2) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op (σ X1) X2) (M.op X0 X1)
       have i₂ := eq185234 X1 X0 X2
       grind)
    | exact superpose eq185234 eq15
    | exact resolve eq15 eq185234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq185234
  have eq190778 : ∀ X0 X1 : G, x ≠ x ∨ x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq171628 x X0 X1
       have i₂ := eq4557
       grind)
    | exact superpose eq4557 eq171628
    | (have j0 := eq171628 x X0 X1
       grind)
    | (have r₁ := eq171628 x X1 x
       have r₂ := eq4557
       grind)
    | exact resolve eq171628 eq4557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557 eq171628
  have eq190800 : ∀ X0 X1 : G, x = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190778 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190778
  have eq191606 : ∀ X1 X2 : G, x = (M.op x X1) ∨ (k X2 (σ (M.op x X1))) = (M.op (σ (M.op x X1)) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq1685 (M.op x X1) (M.op x x) X2
       have i₂ := eq190800 x X1
       grind)
    | exact superpose eq190800 eq1685
    | (have j0 := eq1685 (M.op x X1) X1 X2
       grind)
    | exact resolve eq1685 eq190800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq190800
  have eq191713 : ∀ X1 X2 : G, (M.op (σ x) X2) = (k X2 (σ (M.op x X1))) ∨ x = (M.op x X1) := by
    intro X1 X2
    first
    | (have i₁ := eq191606 X1 X2
       have i₂ := eq139712 x X1 X2
       grind)
    | exact superpose eq139712 eq191606
    | (have j0 := eq191606 X1 X2
       grind)
    | exact resolve eq191606 eq139712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139712 eq191606
  have eq750532 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op (σ x) (M.op (σ X0) X1)) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq186138 x X0 X1
       have i₂ := eq191713 X0 (M.op (σ X0) X1)
       grind)
    | exact superpose eq191713 eq186138
    | (have j1 := eq191713 X0 x
       grind)
    | exact resolve eq186138 eq191713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186138 eq191713
  have eq750542 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq750532 X0 x
       have i₂ := eq345 (σ x) (σ X0) x
       grind)
    | exact superpose eq345 eq750532
    | (have j0 := eq750532 X0 x
       grind)
    | exact resolve eq750532 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq750532
  have eq753588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq750542 y
       grind)
    | exact superpose eq750542 eq14
    | (have j1 := eq750542 y
       grind)
    | (have r₁ := eq14
       have r₂ := eq750542 y
       grind)
    | exact resolve eq14 eq750542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750542
  have eq753643 : x = (M.op x y) := by grind
  clear eq753588
  have eq757253 : ∀ X0 : G, x ≠ x ∨ x = (k y (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq170840 X0 y
       have i₂ := eq753643
       grind)
    | exact superpose eq753643 eq170840
    | (have j0 := eq170840 X0 y
       grind)
    | (have r₁ := eq170840 X0 y
       have r₂ := eq753643
       grind)
    | exact resolve eq170840 eq753643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170840
  have eq757411 : ∀ X0 : G, x = (k y (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have j0 := eq757253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757253
  have eq777070 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq82715 (σ x) y
       have i₂ := eq757411 (σ y)
       grind)
    | exact superpose eq757411 eq82715
    | exact resolve eq82715 eq757411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82715 eq757411
  have eq779874 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq777070
       grind)
    | exact superpose eq777070 eq10
    | exact resolve eq10 eq777070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777070
  have eq782632 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq779874
       grind)
    | exact superpose eq779874 eq14
    | exact resolve eq14 eq779874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779874
  have eq782804 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq782632
       have i₂ := eq753643
       grind)
    | exact superpose eq753643 eq782632
    | exact resolve eq782632 eq753643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753643 eq782632
  have eq782805 : False := by grind
  exact eq782805
