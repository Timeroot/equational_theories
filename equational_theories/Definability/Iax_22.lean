import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

/-- `Equation4423`: `x ◇ (x ◇ y) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4423 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4423 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4423.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X0) := by
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
  have eq17 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) X1) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
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
  have eq19 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X0 X1
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
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
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = (M.op (M.op X2 X2) (M.op (M.op X2 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X2 X1 X0
       grind)
    | (have i₁ := eq20 (M.op X2 X2) X3 X1
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq134 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq31 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X0 ∨ (k X0 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X2 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq139
    | (have j0 := eq139 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq139 (M.op (M.op X2 X2) (M.op X2 X2)) (M.op X2 X2)
       have r₂ := eq8 (M.op X2 X2) (M.op X2 X2) X2
       grind)
    | exact resolve eq139 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X1 (M.op X1 X1) X0
       grind)
    | (have i₁ := eq17 (M.op X1 X1) X3 X2
       have i₂ := eq19 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq19 eq17
    | exact resolve eq17 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X2 X2) X1) ∨ (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 (M.op (M.op X2 X2) X1) X1
       have i₂ := eq17 X2 X1 X0
       grind)
    | exact superpose eq17 eq139
    | (have j0 := eq139 (M.op (M.op X2 X2) X1) X1
       grind)
    | (have r₁ := eq139 (M.op (M.op x x) X1) X1
       have r₂ := eq17 x X1 x
       grind)
    | exact resolve eq139 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X3 X3) (M.op (M.op X2 X2) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op (M.op X2 X2) (M.op X1 X1)) X3
       have i₂ := eq17 X2 (M.op X1 X1) X0
       grind)
    | exact superpose eq17 eq19
    | exact resolve eq19 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq191 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (k (M.op (M.op X2 X2) X1) X1) := by
    intro X1 X2
    first
    | (have j0 := eq185 x X1 X2
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | (have r₁ := eq185 x X1 x
       have r₂ := eq19 x X1 x
       grind)
    | exact resolve eq185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq380 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139 X0 (M.op X1 X1)
       have i₂ := eq28 X0 X1 X2
       grind)
    | (have i₁ := eq139 X0 X0
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq139
    | (have j0 := eq139 X0 X0
       have j1 := eq28 X0 X1 X2
       grind)
    | exact resolve eq139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq139
  have eq388 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq380 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq380 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq380 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x x
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq29 X0 X1
       grind)
    | (have r₁ := eq11 X0 (σ X0)
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq11 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X1) (σ X0) X2
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq600 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq658 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq641 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq641
    | (have j0 := eq641 (τ X0) X1
       grind)
    | exact resolve eq641 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq662 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq666 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq662 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq662
    | (have j0 := eq662 X0 X1
       grind)
    | exact resolve eq662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq717 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X0) X1
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq666
    | (have j0 := eq666 (τ X0) X1
       grind)
    | exact resolve eq666 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq2001 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq637 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq637
    | (have j0 := eq637 (τ X0)
       grind)
    | exact resolve eq637 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq2010 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2001 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2001
    | (have j0 := eq2001 X0
       grind)
    | exact resolve eq2001 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2010 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2010
    | (have j0 := eq2010 X0
       grind)
    | exact resolve eq2010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq6200 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq598
       have i₂ := eq31 x X0 y
       grind)
    | exact superpose eq31 eq598
    | (have j1 := eq31 x X0 x
       grind)
    | exact resolve eq598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq598
  have eq6204 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq6200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6200
  have eq6296 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq6204 (τ X0)
       grind)
    | exact superpose eq6204 eq15
    | exact resolve eq15 eq6204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6204
  have eq6300 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6296 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6296
    | exact resolve eq6296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6296
  have eq6311 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq6300 X0
       have j1 := eq11 X0 (σ x)
       grind)
    | (have r₁ := eq6300 X0
       have r₂ := eq11 X0 (σ x)
       grind)
    | exact resolve eq6300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2016 (σ x)
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq2016
    | (have j0 := eq2016 (σ x)
       grind)
    | (have r₁ := eq2016 (σ x)
       have r₂ := eq6311 (σ x)
       grind)
    | exact resolve eq2016 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6491 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq717 (σ x) X0
       have i₂ := eq6311 (σ x)
       grind)
    | exact superpose eq6311 eq717
    | (have j0 := eq717 (σ x) X0
       grind)
    | exact resolve eq717 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq6501 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (k (σ x) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ x) X1 X0
       have i₂ := eq6311 X0
       grind)
    | exact superpose eq6311 eq388
    | (have j0 := eq388 (σ x) X1 x
       grind)
    | exact resolve eq388 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq6311
  have eq6514 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq6491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6516 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6489
  have eq6522 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6514 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6514
    | exact resolve eq6514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6625 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2016 x
       have i₂ := eq6522 x
       grind)
    | exact superpose eq6522 eq2016
    | (have j0 := eq2016 x
       grind)
    | (have r₁ := eq2016 x
       have r₂ := eq6522 x
       grind)
    | exact resolve eq2016 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522
  have eq6650 : x = (M.op x x) := by grind
  clear eq6625
  have eq7002 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq8
    | exact resolve eq8 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7007 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq19
    | exact resolve eq19 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7030 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq191 x x
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq191
    | exact resolve eq191 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq7055 : ∀ X0 X1 : G, (M.op x x) = (M.op X0 x) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 x x X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq26
    | (have j0 := eq26 X0 X1 x X1
       grind)
    | exact resolve eq26 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7067 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq7055 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq7055
    | (have j0 := eq7055 X0 X1
       grind)
    | exact resolve eq7055 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7055
  have eq9024 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq159 X0 X0 X3 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)
       have i₂ := eq95 X1 X2 (M.op X0 X0) X4
       grind)
    | (have i₁ := eq159 X0 X0 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq95 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq95 eq159
    | exact resolve eq159 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq159
  have eq9073 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9024 X0 X1 X2 X3 X4
       have i₂ := eq7007 (M.op X0 X0) (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq7007 eq9024
    | exact resolve eq9024 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9024
  have eq9189 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x (M.op x X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9073 X0 x X2 X3 X4
       have i₂ := eq7007 x X2
       grind)
    | exact superpose eq7007 eq9073
    | exact resolve eq9073 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9073
  have eq9305 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) (M.op x x)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9189 X0 x X3 X4
       have i₂ := eq7002 x x
       grind)
    | exact superpose eq7002 eq9189
    | exact resolve eq9189 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9189
  have eq9418 : ∀ X0 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X4) x) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9305 X0 X3 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9305
    | exact resolve eq9305 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9305
  have eq9526 : ∀ X3 X4 : G, (M.op (M.op X3 X3) (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X3 X4
    first
    | (have i₁ := eq9418 x X3 x
       have i₂ := eq7007 (M.op x x) x
       grind)
    | exact superpose eq7007 eq9418
    | exact resolve eq9418 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9418
  have eq9632 : ∀ X4 : G, (M.op x (M.op x X4)) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9526 x X4
       have i₂ := eq7007 x (M.op x X4)
       grind)
    | exact superpose eq7007 eq9526
    | exact resolve eq9526 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9526
  have eq9714 : ∀ X4 : G, (M.op x x) = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9632 X4
       have i₂ := eq7002 x X4
       grind)
    | exact superpose eq7002 eq9632
    | exact resolve eq9632 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq9775 : ∀ X4 : G, x = (M.op (M.op x X4) x) := by
    intro X4
    first
    | (have i₁ := eq9714 X4
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9714
    | exact resolve eq9714 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq9886 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X1 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x x X1 X0
       have i₂ := eq9775 x
       grind)
    | exact superpose eq9775 eq67
    | exact resolve eq67 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq9775
  have eq9941 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9886 X0 X1
       have i₂ := eq7007 X1 x
       grind)
    | exact superpose eq7007 eq9886
    | exact resolve eq9886 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9886
  have eq9970 : ∀ X0 X1 : G, x = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9941 X0 X1
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq9941
    | exact resolve eq9941 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9941
  have eq9982 : ∀ X1 : G, x = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq9970 x X1
       have i₂ := eq7007 x (M.op X1 X1)
       grind)
    | exact superpose eq7007 eq9970
    | exact resolve eq9970 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9970
  have eq14615 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op (M.op X3 X3) (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq190 X1 X2 X3 (σ X0)
       have i₂ := eq29 X0 X4
       grind)
    | exact superpose eq29 eq190
    | (have j1 := eq29 X0 X4
       grind)
    | exact resolve eq190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq190
  have eq15228 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) (M.op x (M.op X2 X2))) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14615 X0 X1 X2 x X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq14615
    | (have j0 := eq14615 X0 X1 X2 x X4
       grind)
    | exact resolve eq14615 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615
  have eq15381 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X1) (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq15228 X0 X1 X2 X4
       have i₂ := eq9982 X2
       grind)
    | exact superpose eq9982 eq15228
    | (have j0 := eq15228 X0 X1 X2 X4
       grind)
    | exact resolve eq15228 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15228
  have eq15532 : ∀ X0 X2 X4 : G, (M.op x (M.op X2 X2)) = (M.op (σ X0) x) ∨ (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq15381 X0 x X2 X4
       have i₂ := eq7007 x (M.op X2 X2)
       grind)
    | exact superpose eq7007 eq15381
    | (have j0 := eq15381 X0 x X2 X4
       grind)
    | exact resolve eq15381 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15381
  have eq15675 : ∀ X0 X4 : G, (M.op (σ X0) (σ X4)) = (σ (k X4 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0 X4
    first
    | (have i₁ := eq15532 X0 x X4
       have i₂ := eq9982 x
       grind)
    | exact superpose eq9982 eq15532
    | (have j0 := eq15532 X0 x X4
       grind)
    | exact resolve eq15532 eq9982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15532
  have eq19463 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq19
    | exact resolve eq19 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19524 : x = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9982 (σ x)
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq9982
    | exact resolve eq9982 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9982
  have eq19532 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq148 (σ x) (σ x) X0
       have i₂ := eq6516
       grind)
    | exact superpose eq6516 eq148
    | (have j0 := eq148 (σ x) x X0
       grind)
    | exact resolve eq148 eq6516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq19549 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq19532 X0
       have j1 := eq6501 X0 X0
       grind)
    | (have r₁ := eq19532 X0
       have r₂ := eq6501 (σ x) x
       grind)
    | exact resolve eq19532 eq6501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6501 eq19532
  have eq19597 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq19463 x X1
       have i₂ := eq7007 x X1
       grind)
    | exact superpose eq7007 eq19463
    | exact resolve eq19463 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463
  have eq24810 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19597 (σ y)
       grind)
    | exact superpose eq19597 eq14
    | exact resolve eq14 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24811 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq6516
       have i₂ := eq19597 (σ x)
       grind)
    | exact superpose eq19597 eq6516
    | exact resolve eq6516 eq19597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq25080 : x = (σ x) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq19524
       grind)
    | exact superpose eq19524 eq24811
    | exact resolve eq24811 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524 eq24811
  have eq33070 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq38 x (M.op X0 X0)
       have i₂ := eq19549 X0
       grind)
    | exact superpose eq19549 eq38
    | exact resolve eq38 eq19549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq19549
  have eq33084 : ∀ X0 : G, x = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33070 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq33070
    | exact resolve eq33070 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33070
  have eq43720 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ (M.op x (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op x (σ X0)) X0
       have i₂ := eq7030 (σ X0)
       grind)
    | exact superpose eq7030 eq24
    | exact resolve eq24 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7030
  have eq89782 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X1 (k X2 X1) X3
       have i₂ := eq611 X2 X1 X0
       grind)
    | exact superpose eq611 eq134
    | (have j0 := eq134 X1 X1 X3
       have j1 := eq611 X0 X1 X2
       grind)
    | exact resolve eq134 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq611
  have eq89848 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq89782 X0 X1 X2 X3
       have j1 := eq11 X3 (σ X1)
       grind)
    | (have r₁ := eq89782 X0 X1 X2 X3
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq89782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89782
  have eq90014 : ∀ X1 X2 X3 : G, (M.op x (σ X1)) = (σ (k (k X2 X1) X1)) ∨ (k X3 (σ X1)) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq89848 x X1 X2 X3
       have i₂ := eq7007 x (σ X1)
       grind)
    | exact superpose eq7007 eq89848
    | (have j0 := eq89848 x X1 X2 X3
       grind)
    | exact resolve eq89848 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7007 eq89848
  have eq259053 : ∀ X0 : G, x = (k x (τ (σ (k X0 X0)))) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq33084 (σ X0)
       have i₂ := eq15675 X0 X0
       grind)
    | exact superpose eq15675 eq33084
    | (have j1 := eq15675 X0 x
       grind)
    | exact resolve eq33084 eq15675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15675 eq33084
  have eq259102 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq259053 X0
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq259053
    | (have j0 := eq259053 X0
       grind)
    | exact resolve eq259053 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259053
  have eq259754 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op (σ (τ X0)) x) := by
    intro X0
    first
    | (have i₁ := eq259102 (τ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq259102
    | (have j0 := eq259102 (τ X0)
       grind)
    | exact resolve eq259102 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259102
  have eq259775 : ∀ X0 : G, x = (k x (τ (k X0 X0))) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq259754 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259754
    | (have j0 := eq259754 X0
       grind)
    | exact resolve eq259754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259754
  have eq264392 : ∀ X0 : G, (σ x) = (k (σ x) (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 X0) x
       have i₂ := eq259775 X0
       grind)
    | exact superpose eq259775 eq16
    | (have j1 := eq259775 X0
       grind)
    | exact resolve eq16 eq259775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259775
  have eq264403 : ∀ X0 : G, x = (k x (k X0 X0)) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq264392 X0
       have i₂ := eq25080
       grind)
    | exact superpose eq25080 eq264392
    | (have j0 := eq264392 X0
       grind)
    | exact resolve eq264392 eq25080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25080 eq264392
  have eq265184 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq7067 (k X0 X0) x
       have i₂ := eq264403 X0
       grind)
    | exact superpose eq264403 eq7067
    | (have j0 := eq7067 (k X0 X0) x
       have j1 := eq264403 (k X0 X0)
       grind)
    | exact resolve eq7067 eq264403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067 eq264403
  have eq265188 : ∀ X0 : G, x = (M.op (k X0 X0) x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq265184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265184
  have eq284951 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90014 (τ X1) (τ X0) X2
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq90014
    | (have j0 := eq90014 (τ X1) X2 X2
       grind)
    | exact resolve eq90014 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90014
  have eq284994 : ∀ X0 X1 X2 : G, (M.op x (σ (τ X1))) = (k (σ (τ (k X0 X1))) X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284951 X0 X1 X2
       have i₂ := eq16 X1 (τ (k X0 X1))
       grind)
    | exact superpose eq16 eq284951
    | (have j0 := eq284951 X0 X1 X2
       grind)
    | exact resolve eq284951 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq284951
  have eq285011 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X1))) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq284994 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq284994
    | (have j0 := eq284994 X0 X1 X2
       grind)
    | exact resolve eq284994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284994
  have eq285021 : ∀ X0 X1 X2 : G, (k (k X0 X1) X1) = (M.op x X1) ∨ (k X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285011 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285011
    | (have j0 := eq285011 X0 X1 X2
       grind)
    | exact resolve eq285011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285011
  have eq285026 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (k (k X0 X1) X1) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq285021 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq285021
    | (have j0 := eq285021 X0 X1 X2
       grind)
    | exact resolve eq285021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285021
  have eq291306 : ∀ X0 X1 : G, (M.op x X0) = (k (τ (M.op x (σ X0))) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285026 (τ (M.op x (σ X0))) X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq285026
    | (have j0 := eq285026 X0 X0 X1
       grind)
    | exact resolve eq285026 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285026
  have eq291437 : ∀ X0 X1 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq291306 X0 X1
       have i₂ := eq43720 X0
       grind)
    | exact superpose eq43720 eq291306
    | (have j0 := eq291306 X0 X1
       grind)
    | exact resolve eq291306 eq43720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43720 eq291306
  have eq350747 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x (σ X0))
       have i₂ := eq291437 X0 X1
       grind)
    | exact superpose eq291437 eq10
    | (have j1 := eq291437 X0 X1
       grind)
    | exact resolve eq10 eq291437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291437
  have eq354219 : ∀ X0 : G, (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24810
       have i₂ := eq350747 y X0
       grind)
    | exact superpose eq350747 eq24810
    | (have j1 := eq350747 y X0
       grind)
    | (have r₁ := eq24810
       have r₂ := eq350747 y x
       grind)
    | exact resolve eq24810 eq350747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24810 eq350747
  have eq354273 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq354219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354219
  have eq354486 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2016 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq2016
    | (have j0 := eq2016 y
       grind)
    | (have r₁ := eq2016 y
       have r₂ := eq354273 y
       grind)
    | exact resolve eq2016 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq354564 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq265188 y
       have i₂ := eq354273 y
       grind)
    | exact superpose eq354273 eq265188
    | (have j0 := eq265188 y
       grind)
    | exact resolve eq265188 eq354273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265188 eq354273
  have eq354817 : x = (M.op y x) := by grind
  clear eq354564
  have eq354818 : y = (M.op y y) := by grind
  clear eq354486
  have eq355044 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7002 y x
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq7002
    | exact resolve eq7002 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355072 : x = (M.op x y) := by
    first
    | (have i₁ := eq355044
       have i₂ := eq354817
       grind)
    | exact superpose eq354817 eq355044
    | exact resolve eq355044 eq354817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354817 eq355044
  have eq355526 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq7002 y y
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq7002
    | exact resolve eq7002 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq355553 : y = (M.op x y) := by
    first
    | (have i₁ := eq355526
       have i₂ := eq354818
       grind)
    | exact superpose eq354818 eq355526
    | exact resolve eq355526 eq354818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354818 eq355526
  have eq355781 : x = y := by
    first
    | (have i₁ := eq355553
       have i₂ := eq355072
       grind)
    | exact superpose eq355072 eq355553
    | exact resolve eq355553 eq355072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355072 eq355553
  have eq356245 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq355781
       grind)
    | exact superpose eq355781 eq14
    | exact resolve eq14 eq355781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355781
  have eq356253 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq356245
       have i₂ := eq6650
       grind)
    | exact superpose eq6650 eq356245
    | exact resolve eq356245 eq6650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6650 eq356245
  have eq356255 : False := by grind
  exact eq356255

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pyx_Equation4428 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq19 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq23 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 x X2 X4 X5
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq192 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1206 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X3 (M.op X1 X2)) ∨ (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 (M.op X1 X2) X3
       have i₂ := eq8 X0 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq8 eq192
    | (have j0 := eq192 (M.op X1 X2) X3
       grind)
    | exact resolve eq192 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq192 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1238 : ∀ X1 X2 X3 : G, (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have j0 := eq1206 x X1 X2 X3
       have j1 := eq48 X3 X1 X2 (M.op X1 X2)
       grind)
    | (have r₁ := eq1206 X1 X1 X2 x
       have r₂ := eq48 x X1 (M.op X1 X2) X3
       grind)
    | exact resolve eq1206 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1206
  have eq1271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq14
    | (have j1 := eq52 x x
       grind)
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq13
    | exact resolve eq13 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1358 X0
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq1358
    | exact resolve eq1358 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 X2 X3 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq23
    | exact resolve eq23 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X0 X1
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq19
    | exact resolve eq19 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2035 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2008 X0 X1
       have i₂ := eq1238 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq1238 eq2008
    | exact resolve eq2008 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2043 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq2035
    | exact resolve eq2035 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2047 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2043 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2043
    | exact resolve eq2043 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2049 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq2047
    | exact resolve eq2047 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq2047
  have eq2051 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq1238 X0 X0 X1
       grind)
    | exact superpose eq1238 eq2049
    | exact resolve eq2049 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2049
  have eq14073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1271
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq1271
    | (have j1 := eq12 x (σ x)
       grind)
    | exact resolve eq1271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq14077 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq14073
  have eq14080 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14077
       have i₂ := eq1369 x
       grind)
    | exact superpose eq1369 eq14077
    | exact resolve eq14077 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077
  have eq14087 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq9
    | exact resolve eq9 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq14122 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14087
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq14087
    | exact resolve eq14087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14087
  have eq14123 : x = (M.op x x) := by grind
  clear eq14122
  have eq14514 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1672 x X0 X1 X2
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq1672
    | exact resolve eq1672 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq14520 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq8
    | exact resolve eq8 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14527 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X2 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq23
    | exact resolve eq23 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14123
  have eq14597 : ∀ X2 : G, (M.op x X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq14514 x x X2
       have i₂ := eq14527 x x X2
       grind)
    | exact superpose eq14527 eq14514
    | exact resolve eq14514 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14514 eq14527
  have eq23623 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14597 (σ y)
       grind)
    | exact superpose eq14597 eq14
    | exact resolve eq14 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq42968 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14520 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq14520
    | exact resolve eq14520 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq43408 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42968 X0
       have i₂ := eq2051 X0 X0
       grind)
    | exact superpose eq2051 eq42968
    | exact resolve eq42968 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq42968
  have eq43573 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq43408 X0
       have i₂ := eq14520 X0 X0
       grind)
    | exact superpose eq14520 eq43408
    | exact resolve eq43408 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520 eq43408
  have eq151715 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq43573 y
       grind)
    | exact superpose eq43573 eq23623
    | (have r₁ := eq23623
       have r₂ := eq43573 y
       grind)
    | exact resolve eq23623 eq43573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623 eq43573
  have eq151716 : False := by grind
  exact eq151716

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq19 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq8 x x X4 X5
       have i₂ := eq8 x x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X2 X3 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
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
  clear eq15
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
  have eq51 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq19 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 x X5 X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 X0 X1 x X5
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq82 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X4 x X0 X1
       grind)
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X0 X1 X4 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq8 X4 x X0 X1
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X2 x X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X0 X1 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k X2 (M.op X2 X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X2 X3 X0 X1
       grind)
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X0 X1 X2 X3
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X2 (M.op X2 X3)
       grind)
    | (have r₁ := eq11 X2 (M.op X2 (M.op X2 X3))
       have r₂ := eq22 X2 (M.op X2 X3) X2 X3
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq22 X0 X1 X0 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op X5 (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X7)) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq83 (M.op x X7) X7 X3 X4 X5
       have i₂ := eq51 X0 X1 x X7 X2
       grind)
    | (have i₁ := eq83 (M.op X0 (M.op X0 X1)) X5 X2 X3 X4
       have i₂ := eq51 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq51 eq83
    | exact resolve eq83 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1420 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq1451 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1473 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op X5 (M.op X6 (M.op X6 X7))) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X4) := by
    intro X0 X1 X2 X4 X5 X6 X7
    first
    | (have i₁ := eq97 X6 X7 X5 (M.op x X4) X4
       have i₂ := eq51 X0 X1 x X4 X2
       grind)
    | (have i₁ := eq97 X0 X1 X2 (M.op X0 (M.op X0 X1)) X5
       have i₂ := eq51 X0 X1 X2 x X5
       grind)
    | exact superpose eq51 eq97
    | exact resolve eq97 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X6) X7) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq60 (M.op x X6) X6 X3 X4 X7
       have i₂ := eq97 X1 X2 X0 x X6
       grind)
    | (have i₁ := eq60 X2 (M.op X0 (M.op X0 X1)) X2 X3 x
       have i₂ := eq97 X0 X1 X2 X4 x
       grind)
    | exact superpose eq97 eq60
    | exact resolve eq60 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq97
  have eq8696 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1451 (τ X0) (τ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq1451
    | (have j0 := eq1451 (τ X0) (τ X1)
       grind)
    | exact resolve eq1451 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1451
  have eq8703 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8696 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8696
    | (have j0 := eq8696 X0 X1
       grind)
    | exact resolve eq8696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696
  have eq8705 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8703 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8703
    | (have j0 := eq8703 X0 X1
       grind)
    | exact resolve eq8703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8703
  have eq8706 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8705 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8705
    | (have j0 := eq8705 X0 X1
       grind)
    | exact resolve eq8705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8707 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8706 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8706
    | (have j0 := eq8706 X0 X1
       grind)
    | exact resolve eq8706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq9048 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq9132 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9048 X2 (M.op X2 x)
       have i₂ := eq82 X2 x X0 X1 X2
       grind)
    | (have i₁ := eq9048 X2 x
       have i₂ := eq82 X0 X1 X2 x x
       grind)
    | exact superpose eq82 eq9048
    | exact resolve eq9048 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq9048
  have eq9331 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (M.op X1 X2))
       have i₂ := eq9132 X1 X2 (σ X0)
       grind)
    | exact superpose eq9132 eq38
    | exact resolve eq38 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9334 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9331 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9331
    | exact resolve eq9331 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331
  have eq26832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1420
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq1420
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq26833 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26832
  have eq42138 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9132 (σ x) (σ y) X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq9132
    | exact resolve eq9132 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq110776 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42138 X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq42138
    | exact resolve eq42138 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26833 eq42138
  have eq110799 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq110776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110776
  have eq112614 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (σ y)
       have i₂ := eq110799 (σ X0)
       grind)
    | exact superpose eq110799 eq38
    | exact resolve eq38 eq110799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq110799
  have eq112625 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112614 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq112614
    | exact resolve eq112614 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112614
  have eq112628 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112625 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112625
    | exact resolve eq112625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112625
  have eq114405 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 y
       have i₂ := eq112628 X0
       grind)
    | exact superpose eq112628 eq8707
    | (have j0 := eq8707 X0 y
       grind)
    | (have r₁ := eq8707 y y
       have r₂ := eq112628 y
       grind)
    | exact resolve eq8707 eq112628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112628
  have eq117676 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq114405 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114405
  have eq118561 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y y
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq19
    | exact resolve eq19 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq294475 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq118561 (M.op x X1) X1
       have i₂ := eq118561 x X1
       grind)
    | exact superpose eq118561 eq118561
    | exact resolve eq118561 eq118561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118561
  have eq295500 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq294475 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294475
  have eq406531 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295500 x
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq295500
    | exact resolve eq295500 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117676 eq295500
  have eq407179 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq406531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406531
  have eq409295 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 x x x X0 X1 y x
       have i₂ := eq407179 (M.op (M.op (M.op x (M.op x x)) x) x)
       grind)
    | exact superpose eq407179 eq1263
    | exact resolve eq1263 eq407179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq407179
  have eq411137 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq409295 X0 (M.op X0 x)
       have i₂ := eq409295 X0 x
       grind)
    | exact superpose eq409295 eq409295
    | exact resolve eq409295 eq409295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409295
  have eq412522 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq411137 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411137
  have eq414872 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq412522 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412522
  have eq414873 : y = (M.op x y) := by grind
  clear eq414872
  have eq416374 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq8
    | exact resolve eq8 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq21
    | exact resolve eq21 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq416385 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq22
    | exact resolve eq22 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq416389 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq51
    | exact resolve eq51 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq416707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1473 X1 X2 X3 X4 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1473
    | exact resolve eq1473 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq416722 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 (M.op x y)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X2 x y X0 X1 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1612
    | exact resolve eq1612 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq416766 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9334 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq9334
    | exact resolve eq9334 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq416861 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq416766 X0
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416766
    | exact resolve eq416766 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416766
  have eq416879 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416722 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416722
    | exact resolve eq416722 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416722
  have eq416890 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416707 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416707
    | exact resolve eq416707 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416707
  have eq417009 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416389 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416389
    | exact resolve eq416389 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416389
  have eq417011 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq416385 X0 X1
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416385
    | exact resolve eq416385 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416385
  have eq417013 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416383 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416383
    | exact resolve eq416383 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416383
  have eq417017 : ∀ X2 X3 X4 : G, (M.op y y) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq416879 x x X2 X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416879
    | exact resolve eq416879 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416879
  have eq417028 : ∀ X0 X3 X4 : G, (M.op X0 y) = (M.op (M.op (M.op y y) X3) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq416890 X0 x x X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416890
    | exact resolve eq416890 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416374 eq416890
  have eq417136 : ∀ X2 : G, y = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq417013 x x X2
       have i₂ := eq417011 x x
       grind)
    | exact superpose eq417011 eq417013
    | exact resolve eq417013 eq417011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417011 eq417013
  have eq417141 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417028 X0 x x
       have i₂ := eq417017 y x x
       grind)
    | exact superpose eq417017 eq417028
    | exact resolve eq417028 eq417017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417017 eq417028
  have eq417191 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417141 X0
       have i₂ := eq417136 y
       grind)
    | exact superpose eq417136 eq417141
    | exact resolve eq417141 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417141
  have eq431902 : ∀ X0 : G, (τ y) ≠ X0 ∨ (τ y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 (τ y)
       have i₂ := eq416861 X0
       grind)
    | exact superpose eq416861 eq8707
    | (have j0 := eq8707 X0 (τ y)
       grind)
    | (have r₁ := eq8707 (τ y) (τ y)
       have r₂ := eq416861 (τ y)
       grind)
    | exact resolve eq8707 eq416861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707 eq416861
  have eq866962 : (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have j0 := eq431902 (τ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431902
  have eq868700 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq417009 (τ y) (τ y) X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq417009
    | exact resolve eq417009 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417009
  have eq868706 : ∀ X0 : G, (τ y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq868700 X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq868700
    | exact resolve eq868700 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866962 eq868700
  have eq868872 : y = (τ y) := by
    first
    | (have i₁ := eq868706 x
       have i₂ := eq417136 x
       grind)
    | exact superpose eq417136 eq868706
    | exact resolve eq868706 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417136 eq868706
  have eq870623 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq868872
       grind)
    | exact superpose eq868872 eq10
    | exact resolve eq10 eq868872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868872
  have eq872866 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq14
    | exact resolve eq14 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872923 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq872866
       have i₂ := eq417191 (σ x)
       grind)
    | exact superpose eq417191 eq872866
    | exact resolve eq872866 eq417191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417191 eq872866
  have eq872931 : y ≠ (σ y) := by
    first
    | (have i₁ := eq872923
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq872923
    | exact resolve eq872923 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414873 eq872923
  have eq872933 : y ≠ y := by
    first
    | (have i₁ := eq872931
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq872931
    | (have r₁ := eq872931
       have r₂ := eq870623
       grind)
    | exact resolve eq872931 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870623 eq872931
  have eq872934 : False := by grind
  exact eq872934
