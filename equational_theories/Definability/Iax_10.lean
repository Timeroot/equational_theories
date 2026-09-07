import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation978 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law978 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq8 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x x X0
       have i₂ := eq19 x x X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq19 X0 X1 X2
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (k X2 (M.op (M.op X0 (M.op X1 X1)) X0)) := by
    intro X0 X1 X2
    grind
  have eq56 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X1 X1)
       have i₂ := eq19 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 x X0 X2
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X2 X3 : G, (M.op X0 X0) = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq51 X0 x X2 X3
       have i₂ := eq56 x X0
       grind)
    | exact superpose eq56 eq51
    | (have j0 := eq51 X0 x X2 X3
       grind)
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq8
    | exact resolve eq8 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq142 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
       have i₂ := eq18 X3 X2 X0 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq182 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq142 X0 X1 x X3 X4 x
       have i₂ := eq124 (M.op X3 X0) x x
       grind)
    | exact superpose eq124 eq142
    | exact resolve eq142 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq326 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (σ X1)
       grind)
    | exact superpose eq60 eq39
    | exact resolve eq39 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq50 X0 (σ X0)
       grind)
    | exact superpose eq50 eq31
    | exact resolve eq31 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq31
  have eq774 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq326 X0 (σ X1)
       grind)
    | exact superpose eq326 eq39
    | exact resolve eq39 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq326
  have eq2259 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
       have i₂ := eq182 X2 X4 X1 X0
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2260 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq2259 x X1 X2 x X4
       have i₂ := eq124 X1 x x
       grind)
    | exact superpose eq124 eq2259
    | exact resolve eq2259 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2488 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 X1 X2 x
       have i₂ := eq2260 X0 X1 x
       grind)
    | (have i₁ := eq124 X2 X1 X2
       have i₂ := eq2260 X2 X2 x
       grind)
    | exact superpose eq2260 eq124
    | exact resolve eq124 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2260
  have eq4852 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq415
    | (have j0 := eq415 X1 (M.op X0 X0)
       grind)
    | exact resolve eq415 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4857 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq774 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq774 eq415
    | (have j0 := eq415 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq415 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq4952 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq415 X0 (τ X1)
       grind)
    | exact superpose eq415 eq17
    | (have j1 := eq415 X0 (τ X1)
       grind)
    | exact resolve eq17 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq415
  have eq4974 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq4857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4978 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4852 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq4989 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4952 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4952
    | (have j0 := eq4952 X0 X1
       grind)
    | exact resolve eq4952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5025 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4974 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq4974
    | exact resolve eq4974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5035 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4989 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4989
    | (have j0 := eq4989 X0 X1
       grind)
    | exact resolve eq4989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989
  have eq5058 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq432
       have i₂ := eq62 X0 x y
       grind)
    | exact superpose eq62 eq432
    | (have j1 := eq62 (σ x) x (σ y)
       grind)
    | exact resolve eq432 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq432
  have eq5064 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq5058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq5173 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (σ (M.op X0 X0)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2488 X2 X2 X1
       have i₂ := eq4978 X0 X2
       grind)
    | exact superpose eq4978 eq2488
    | exact resolve eq2488 eq4978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488 eq4978
  have eq30475 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2
       have i₂ := eq5035 X2 X0
       grind)
    | exact superpose eq5035 eq50
    | (have j1 := eq5035 X1 X0
       grind)
    | exact resolve eq50 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq30754 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46085 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq60 X2 X2
       have i₂ := eq30475 X0 x X2
       grind)
    | (have i₁ := eq60 X0 X2
       have i₂ := eq30475 (M.op X0 X0) x X2
       grind)
    | exact superpose eq30475 eq60
    | (have j1 := eq30475 X0 X3 X2
       grind)
    | exact resolve eq60 eq30475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq30475
  have eq66856 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46085 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46085
  have eq66862 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66856 X0 X1
       have j1 := eq5035 X1 X0
       grind)
    | (have r₁ := eq66856 (k X1 X1) X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 X1 X0
       have r₂ := eq5035 X0 X1
       grind)
    | (have r₁ := eq66856 (M.op X0 X0) X1
       have r₂ := eq5035 X0 (M.op X1 X1)
       grind)
    | exact resolve eq66856 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq66856
  have eq67900 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30754 X2 X1
       have i₂ := eq66862 X1 X0
       grind)
    | exact superpose eq66862 eq30754
    | (have j0 := eq30754 X2 X1
       grind)
    | (have r₁ := eq30754 X0 (M.op X1 X1)
       have r₂ := eq66862 (M.op X1 X1) X1
       grind)
    | exact resolve eq30754 eq66862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30754 eq66862
  have eq69448 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5025 (σ x) X0
       have i₂ := eq5064 X1
       grind)
    | exact superpose eq5064 eq5025
    | (have j1 := eq5064 X1
       grind)
    | exact resolve eq5025 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025 eq5064
  have eq69767 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69448 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq69448
    | (have j0 := eq69448 X0 X0
       grind)
    | exact resolve eq69448 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69448
  have eq69776 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq69767 X0 X0
       have j1 := eq67900 X0 y X0
       grind)
    | (have r₁ := eq69767 X0 x
       have r₂ := eq67900 X0 y x
       grind)
    | (have r₁ := eq69767 X0 X0
       have r₂ := eq67900 X0 y x
       grind)
    | exact resolve eq69767 eq67900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67900 eq69767
  have eq70032 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq69776 (M.op X0 X0)
       grind)
    | exact superpose eq69776 eq8
    | exact resolve eq8 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70038 : ∀ X0 : G, y = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5173 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq69776 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq69776 eq5173
    | exact resolve eq5173 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173
  have eq70125 : y = (σ y) := by
    first
    | (have i₁ := eq70038 x
       have i₂ := eq69776 x
       grind)
    | exact superpose eq69776 eq70038
    | exact resolve eq70038 eq69776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69776 eq70038
  have eq70822 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq70125
       grind)
    | exact superpose eq70125 eq14
    | exact resolve eq14 eq70125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70125
  have eq70856 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq70822
       have i₂ := eq70032 (σ x)
       grind)
    | exact superpose eq70032 eq70822
    | exact resolve eq70822 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70822
  have eq70866 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq70856
       have i₂ := eq70032 x
       grind)
    | exact superpose eq70032 eq70856
    | exact resolve eq70856 eq70032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70032 eq70856
  have eq70867 : False := by grind
  exact eq70867

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1027 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
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
  have eq46 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq561 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq562 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq569 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq562 (σ X0) (σ X1)
       grind)
    | exact superpose eq562 eq13
    | exact resolve eq13 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq562 X0 X1
       grind)
    | exact superpose eq562 eq569
    | exact resolve eq569 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq569
  have eq1562 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq583 x y
       grind)
    | exact superpose eq583 eq14
    | (have r₁ := eq14
       have r₂ := eq583 x y
       grind)
    | exact resolve eq14 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq1587 : False := by grind
  exact eq1587

/-- `Equation1032`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1032 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1032 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1032.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq565 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq566 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq566 (σ X0) (σ X1)
       grind)
    | exact superpose eq566 eq13
    | exact resolve eq13 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq566 X0 X1
       grind)
    | exact superpose eq566 eq574
    | exact resolve eq574 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq574
  have eq1257 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq590 x y
       grind)
    | exact superpose eq590 eq14
    | (have r₁ := eq14
       have r₂ := eq590 x y
       grind)
    | exact resolve eq14 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1283 : False := by grind
  exact eq1283

/-- `Equation1033`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1033 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1033 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1033.models_iff G M).mp hM
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
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
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
  have eq686 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq687 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq686 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq687 (σ X0) (σ X1)
       grind)
    | exact superpose eq687 eq13
    | exact resolve eq13 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq687 X0 X1
       grind)
    | exact superpose eq687 eq695
    | exact resolve eq695 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq695
  have eq1807 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq710 x y
       grind)
    | exact superpose eq710 eq14
    | (have r₁ := eq14
       have r₂ := eq710 x y
       grind)
    | exact resolve eq14 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1840 : False := by grind
  exact eq1840

/-- `Equation1037`: `x = x ◇ ((y ◇ (x ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pyx_pxy_Equation1037 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1037 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1037.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq8 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) x)
       have i₂ := eq8 (M.op X0 (M.op X1 X1)) x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq13
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq32
    | exact resolve eq32 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq12 X0 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = X1 ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X2
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq51
  have eq118 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X1 x
       have i₂ := eq22 (M.op X1 X1) X1
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq118 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq21 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq118 X0 (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq22 x (M.op X0 X0)
       grind)
    | exact superpose eq22 eq118
    | exact resolve eq118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq159 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq150 X0
       grind)
    | exact superpose eq150 eq144
    | exact resolve eq144 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq196 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0 X0
       have i₂ := eq150 X0
       grind)
    | exact superpose eq150 eq22
    | exact resolve eq22 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq229 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X1 X1)
       have i₂ := eq48 X1 X0 (M.op X1 X1)
       grind)
    | exact superpose eq48 eq22
    | (have j1 := eq48 X1 X0 x
       grind)
    | exact resolve eq22 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq243 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X0
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq229
    | (have j0 := eq229 X0 X1
       grind)
    | exact resolve eq229 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq253 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq267 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq11
    | (have j0 := eq11 X0 X1
       grind)
    | exact resolve eq11 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq22
    | exact resolve eq22 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq281 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 X0
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq21
    | exact resolve eq21 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq290 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq196 X0
       grind)
    | exact superpose eq196 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq14
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq350 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq327
       have i₂ := eq196 x
       grind)
    | exact superpose eq196 eq327
    | exact resolve eq327 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq530 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) X2) ∨ (M.op (σ X0) X2) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq38 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq38 eq13
    | (have j1 := eq38 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq568 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X1)
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq11
    | (have j0 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq568 X0 X1
       grind)
    | (have r₁ := eq568 X0 X1
       have r₂ := eq196 X0
       grind)
    | exact resolve eq568 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq664 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X0)
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq11
    | (have j0 := eq11 X0 (M.op X1 X0)
       grind)
    | exact resolve eq11 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq196 X0
       grind)
    | exact resolve eq664 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq664
  have eq686 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq281 X0 X1
       grind)
    | exact superpose eq281 eq677
    | exact resolve eq677 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq677
  have eq1036 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq686 (M.op X1 X0) X0
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq686
    | exact resolve eq686 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq1207 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 (σ X0)) X0
       have i₂ := eq1036 (σ X0) X1
       grind)
    | exact superpose eq1036 eq20
    | exact resolve eq20 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1036
  have eq1210 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1207
    | exact resolve eq1207 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq3089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350
       have i₂ := eq253 y x
       grind)
    | exact superpose eq253 eq350
    | (have j1 := eq253 (σ y) (σ x)
       grind)
    | exact resolve eq350 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq3090 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3089
  have eq13173 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1210 y (σ x)
       have i₂ := eq3090
       grind)
    | exact superpose eq3090 eq1210
    | exact resolve eq1210 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq3090
  have eq13241 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13173
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13173
    | exact resolve eq13173 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13173
  have eq13542 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253 y x
       have i₂ := eq13241
       grind)
    | exact superpose eq13241 eq253
    | (have j0 := eq253 y x
       grind)
    | exact resolve eq253 eq13241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq13241
  have eq13552 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13542
  have eq14584 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159 x y
       have i₂ := eq13552
       grind)
    | exact superpose eq13552 eq159
    | exact resolve eq159 eq13552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14598 : (k x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq577 x y
       have i₂ := eq13552
       grind)
    | exact superpose eq13552 eq577
    | exact resolve eq577 eq13552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq13552
  have eq14631 : x = (M.op x y) := by grind
  clear eq14584
  have eq14632 : (k x y) = (M.op y x) := by
    first
    | (have j1 := eq267 x y
       grind)
    | (have r₁ := eq14598
       have r₂ := eq267 x y
       grind)
    | exact resolve eq14598 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq14598
  have eq14949 : y = (M.op y x) := by
    first
    | (have i₁ := eq270 y x
       have i₂ := eq14631
       grind)
    | exact superpose eq14631 eq270
    | exact resolve eq270 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq22126 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq530 x X0 (σ y)
       grind)
    | (have i₁ := eq14
       have i₂ := eq530 x y x
       grind)
    | exact superpose eq530 eq14
    | (have j1 := eq530 x X0 (σ y)
       grind)
    | exact resolve eq14 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq22383 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22126 X0
       have i₂ := eq14631
       grind)
    | exact superpose eq14631 eq22126
    | (have j0 := eq22126 X0
       grind)
    | exact resolve eq22126 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22126
  have eq22466 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22383 X0
       have j1 := eq290 x X0
       grind)
    | (have r₁ := eq22383 x
       have r₂ := eq290 x x
       grind)
    | exact resolve eq22383 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq22383
  have eq22497 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22466 X0
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq22466
    | (have j0 := eq22466 y
       grind)
    | exact resolve eq22466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22466
  have eq22510 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22497 X0
       have i₂ := eq14632
       grind)
    | exact superpose eq14632 eq22497
    | (have j0 := eq22497 X0
       grind)
    | exact resolve eq22497 eq14632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22497
  have eq22517 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22510 X0
       have i₂ := eq14949
       grind)
    | exact superpose eq14949 eq22510
    | (have j0 := eq22510 X0
       grind)
    | exact resolve eq22510 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510
  have eq51718 : (σ y) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22517
  have eq51726 : (σ y) ≠ (σ (M.op y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51718
       have i₂ := eq14632
       grind)
    | exact superpose eq14632 eq51718
    | exact resolve eq51718 eq14632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14632 eq51718
  have eq51827 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51726
       have i₂ := eq14949
       grind)
    | exact superpose eq14949 eq51726
    | exact resolve eq51726 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14949 eq51726
  have eq51828 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq51827
  have eq51911 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq51828
       grind)
    | exact superpose eq51828 eq14
    | exact resolve eq14 eq51828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51967 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq159 (σ x) (σ y)
       have i₂ := eq51828
       grind)
    | exact superpose eq51828 eq159
    | exact resolve eq159 eq51828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq52114 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq51911
       have i₂ := eq14631
       grind)
    | exact superpose eq14631 eq51911
    | exact resolve eq51911 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631 eq51911
  have eq52767 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq51828
       have i₂ := eq51967
       grind)
    | exact superpose eq51967 eq51828
    | exact resolve eq51828 eq51967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51828 eq51967
  have eq52931 : False := by grind
  exact eq52931

/-- `Equation1042`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1042 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1042 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1042.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X1)) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op x (M.op X0 x)) x)
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 (M.op X0 X2)) X0 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
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
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq43 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq63 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq43 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq43 eq13
    | (have j1 := eq43 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq199 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq25 X0 X0
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq274 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq200 X0 (τ X1)
       grind)
    | exact superpose eq200 eq15
    | exact resolve eq15 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq200
  have eq907 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq969 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq907
    | (have j0 := eq907 X0 X1
       grind)
    | exact resolve eq907 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1030 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 X1 X1
       have i₂ := eq969 X0 X1
       grind)
    | exact superpose eq969 eq274
    | (have j1 := eq969 X2 X0
       grind)
    | exact resolve eq274 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq969
  have eq1479 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq22
    | exact resolve eq22 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1491 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1479 X0 X1
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq1479
    | exact resolve eq1479 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1479
  have eq1670 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq127 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq127
    | (have j0 := eq127 (τ X0)
       grind)
    | exact resolve eq127 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq127
  have eq1686 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1670 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1670
    | (have j0 := eq1670 X0
       grind)
    | exact resolve eq1670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1695 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1686 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1686
    | (have j0 := eq1686 X0
       grind)
    | exact resolve eq1686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq2159 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y X0
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 X0 y X0
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2232 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2159 X0
       have j1 := eq1030 y X0 x
       grind)
    | (have r₁ := eq2159 X0
       have r₂ := eq1030 y x x
       grind)
    | exact resolve eq2159 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq2159
  have eq2260 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1695 (σ y)
       have i₂ := eq2232 (σ y)
       grind)
    | exact superpose eq2232 eq1695
    | (have j0 := eq1695 (σ y)
       grind)
    | (have r₁ := eq1695 (σ y)
       have r₂ := eq2232 (σ y)
       grind)
    | exact resolve eq1695 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2275 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ y)
       have i₂ := eq2232 (σ X0)
       grind)
    | exact superpose eq2232 eq32
    | exact resolve eq32 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2232
  have eq2280 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2260
  have eq2281 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2275 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2275
    | exact resolve eq2275 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2405 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1695 y
       have i₂ := eq2281 y
       grind)
    | exact superpose eq2281 eq1695
    | (have j0 := eq1695 y
       grind)
    | (have r₁ := eq1695 y
       have r₂ := eq2281 y
       grind)
    | exact resolve eq1695 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq2281
  have eq2422 : y = (M.op y y) := by grind
  clear eq2405
  have eq2534 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq1491 y X0
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq1491
    | exact resolve eq1491 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2985 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1491 (σ y) X0
       have i₂ := eq2280
       grind)
    | exact superpose eq2280 eq1491
    | exact resolve eq1491 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq3866 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 y
       have i₂ := eq2534 X0
       grind)
    | exact superpose eq2534 eq21
    | exact resolve eq21 eq2534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2534
  have eq4146 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0 X0
       have i₂ := eq3866 X0
       grind)
    | exact superpose eq3866 eq22
    | exact resolve eq22 eq3866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq4175 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4146 X0
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq4146
    | exact resolve eq4146 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq4146
  have eq11180 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0 (σ y)
       have i₂ := eq2985 X0
       grind)
    | exact superpose eq2985 eq21
    | exact resolve eq21 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2985
  have eq11377 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0 X0
       have i₂ := eq11180 X0
       grind)
    | exact superpose eq11180 eq22
    | exact resolve eq22 eq11180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11180
  have eq11425 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11377 X0
       have i₂ := eq2280
       grind)
    | exact superpose eq2280 eq11377
    | exact resolve eq11377 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280 eq11377
  have eq11744 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11425 (σ x)
       grind)
    | exact superpose eq11425 eq14
    | exact resolve eq14 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11425
  have eq11759 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11744
       have i₂ := eq4175 x
       grind)
    | exact superpose eq4175 eq11744
    | exact resolve eq11744 eq4175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175 eq11744
  have eq11760 : False := by grind
  exact eq11760

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation1043 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq8 X0 X2 X3
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
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq78 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq47 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq110 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq21 X0 X1 X3 X4
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq21 X0 X1 X2 X3
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq117 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq115
    | exact resolve eq115 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X0 X1 X2 x x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq110
    | exact resolve eq110 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq154 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq83 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq154 (σ X0)
       grind)
    | exact superpose eq154 eq13
    | exact resolve eq13 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq201 X0
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq201
    | exact resolve eq201 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq245 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq43 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq11 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X1) (σ X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq83
    | (have j1 := eq43 X1 X0
       grind)
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq258 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq260 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq263 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq245 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq277 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq260 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq260
    | (have j0 := eq260 X0 X1
       grind)
    | exact resolve eq260 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq278 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq154 X0
       grind)
    | exact superpose eq154 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq376 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq117 (σ X0) (σ X0)
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq117
    | exact resolve eq117 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq971 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X1
       have i₂ := eq911 X0 X1
       grind)
    | exact superpose eq911 eq376
    | (have j1 := eq911 X1 X0
       grind)
    | exact resolve eq376 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq980 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq971
    | (have j0 := eq971 X0 X1
       grind)
    | exact resolve eq971 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq971
  have eq1102 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq911 X2 X0
       grind)
    | exact superpose eq911 eq278
    | (have j0 := eq278 X0 X1
       have j1 := eq911 X2 X0
       grind)
    | exact resolve eq278 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq911
  have eq1114 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1102 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq3203 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq78 x y X0
       grind)
    | exact superpose eq78 eq14
    | (have j1 := eq78 X0 y X0
       grind)
    | exact resolve eq14 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3375 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3203 X0
       have j1 := eq1114 y X0 x
       grind)
    | (have r₁ := eq3203 X0
       have r₂ := eq1114 y x x
       grind)
    | exact resolve eq3203 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq3203
  have eq3493 : ∀ X0 : G, (k X0 (σ y)) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq84 X0 X0
       have i₂ := eq3375 X0
       grind)
    | exact superpose eq3375 eq84
    | exact resolve eq84 eq3375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq3375
  have eq3537 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq4229 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq3537 (σ X0)
       grind)
    | (have i₁ := eq28 X0 (σ y)
       have i₂ := eq3537 (σ X0)
       grind)
    | exact superpose eq3537 eq28
    | exact resolve eq28 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3537
  have eq4277 : ∀ X0 : G, (k X0 (τ (σ X0))) = (k (τ (σ X0)) y) := by
    intro X0
    first
    | (have i₁ := eq4229 X0
       have i₂ := eq20 (σ X0) y
       grind)
    | exact superpose eq20 eq4229
    | exact resolve eq4229 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4229
  have eq4309 : ∀ X0 : G, (k X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq4277 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4277
    | exact resolve eq4277 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277
  have eq4604 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq4309 X0
       grind)
    | (have i₁ := eq154 y
       have i₂ := eq4309 y
       grind)
    | exact superpose eq4309 eq154
    | exact resolve eq154 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq4309
  have eq58945 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq277 y x
       grind)
    | exact superpose eq277 eq14
    | (have j1 := eq277 y x
       grind)
    | exact resolve eq14 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq59166 : (σ y) = (σ (M.op y y)) := by
    first
    | (have j1 := eq980 y x
       grind)
    | (have r₁ := eq58945
       have r₂ := eq980 y x
       grind)
    | exact resolve eq58945 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq58945
  have eq59516 : (τ (σ y)) = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq59166
       grind)
    | exact superpose eq59166 eq9
    | exact resolve eq9 eq59166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59166
  have eq59617 : y = (M.op y y) := by
    first
    | (have i₁ := eq59516
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq59516
    | exact resolve eq59516 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59516
  have eq60006 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq118 y y x
       have i₂ := eq59617
       grind)
    | exact superpose eq59617 eq118
    | exact resolve eq118 eq59617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60042 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq60006 X0
       have i₂ := eq117 y X0
       grind)
    | exact superpose eq117 eq60006
    | exact resolve eq60006 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq60006
  have eq62141 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y y
       have i₂ := eq60042 X0
       grind)
    | exact superpose eq60042 eq8
    | exact resolve eq8 eq60042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62247 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq62141 X0
       have i₂ := eq59617
       grind)
    | exact superpose eq59617 eq62141
    | exact resolve eq62141 eq59617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62141
  have eq64053 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq60042 X0
       have i₂ := eq62247 X0
       grind)
    | exact superpose eq62247 eq60042
    | exact resolve eq60042 eq62247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60042
  have eq64164 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq118 y X1 X0
       have i₂ := eq62247 (M.op X0 (M.op X1 y))
       grind)
    | exact superpose eq62247 eq118
    | exact resolve eq118 eq62247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq64200 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64164 X0 X0
       have i₂ := eq62247 X0
       grind)
    | exact superpose eq62247 eq64164
    | exact resolve eq64164 eq62247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64164
  have eq65333 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq83 y X0
       have i₂ := eq64053 X0
       grind)
    | exact superpose eq64053 eq83
    | exact resolve eq83 eq64053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq64053
  have eq65475 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq65333 X0
       grind)
    | (have r₁ := eq65333 X0
       have r₂ := eq59617
       grind)
    | exact resolve eq65333 eq59617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59617 eq65333
  have eq66663 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq65475 (τ X0)
       grind)
    | exact superpose eq65475 eq16
    | exact resolve eq16 eq65475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq65475
  have eq67510 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X0
       have i₂ := eq64200 X1 X0
       grind)
    | exact superpose eq64200 eq8
    | exact resolve eq8 eq64200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64200
  have eq68933 : ∀ X0 X1 : G, (M.op X1 (k X0 y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67510 X0 X1
       have i₂ := eq4604 X0
       grind)
    | exact superpose eq4604 eq67510
    | exact resolve eq67510 eq4604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604 eq67510
  have eq73857 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq68933 (σ y) X0
       have i₂ := eq66663 y
       grind)
    | exact superpose eq66663 eq68933
    | exact resolve eq68933 eq66663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66663 eq68933
  have eq75382 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73857 (σ x)
       grind)
    | exact superpose eq73857 eq14
    | exact resolve eq14 eq73857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73857
  have eq75405 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq75382
       have i₂ := eq62247 x
       grind)
    | exact superpose eq62247 eq75382
    | exact resolve eq75382 eq62247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62247 eq75382
  have eq75406 : False := by grind
  exact eq75406

/-- `Equation1053`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1053 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1053 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1053.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X0 (M.op (M.op X1 (M.op X1 X2)) X2)
       have i₂ := eq8 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) X1 X2
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
  have eq118 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
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
  have eq186 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
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
  have eq187 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq467 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq467
    | (have j0 := eq467 X0 X1
       grind)
    | exact resolve eq467 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq1255 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq187 (M.op X0 X0)
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq187
    | (have j0 := eq187 (M.op X0 X0)
       grind)
    | exact resolve eq187 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1269 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq187 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq187
    | (have j0 := eq187 (τ X0)
       grind)
    | exact resolve eq187 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq187
  have eq1282 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1255 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1287 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1269 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1269
    | (have j0 := eq1269 X0
       grind)
    | exact resolve eq1269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1296 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1287 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1287
    | (have j0 := eq1287 X0
       grind)
    | exact resolve eq1287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1474 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq1282 X0
       grind)
    | exact superpose eq1282 eq24
    | exact resolve eq24 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1551 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1474 X0 X1
       have i₂ := eq512 X2 X0
       grind)
    | exact superpose eq512 eq1474
    | (have j1 := eq512 X2 X0
       grind)
    | exact resolve eq1474 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq1474
  have eq1651 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq186 y X0 x
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 y X0 x
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1678 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1651 X0
       have j1 := eq1551 y X0 x
       grind)
    | (have r₁ := eq1651 X0
       have r₂ := eq1551 y x x
       grind)
    | exact resolve eq1651 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq1651
  have eq1691 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq118 (σ y) x
       have i₂ := eq1678 (σ y)
       grind)
    | exact superpose eq1678 eq118
    | exact resolve eq118 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1702 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1678 (σ x)
       grind)
    | exact superpose eq1678 eq14
    | exact resolve eq14 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1714 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1691 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1691
    | exact resolve eq1691 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1836 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1296 y
       have i₂ := eq1714 y
       grind)
    | exact superpose eq1714 eq1296
    | (have j0 := eq1296 y
       grind)
    | (have r₁ := eq1296 y
       have r₂ := eq1714 y
       grind)
    | exact resolve eq1296 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq1714
  have eq1852 : y = (M.op y y) := by grind
  clear eq1836
  have eq1961 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq1852
       grind)
    | exact superpose eq1852 eq24
    | exact resolve eq24 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1852
  have eq2363 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1702
       have i₂ := eq1961 x
       grind)
    | exact superpose eq1961 eq1702
    | exact resolve eq1702 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq1961
  have eq2364 : False := by grind
  exact eq2364
