import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3495 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3495 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq169 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq169 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq169 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq169 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq175 (σ X0) (σ X1)
       grind)
    | exact superpose eq175 eq13
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq197
    | exact resolve eq197 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq197
  have eq1870 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have r₁ := eq14
       have r₂ := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1902 : False := by grind
  exact eq1902

/-- `Equation3503`: `x ◇ x = y ◇ ((z ◇ w) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation3503 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3503 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op (M.op X5 X6) X3)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8 X3 X4 X5 X6
       have i₂ := eq8 X3 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X1 X2) X0) X3 x x
       have i₂ := eq8 X0 (M.op x x) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq8 X0 (M.op (M.op x x) X0) x x
       grind)
    | (have i₁ := eq26 X0 x x X3
       have i₂ := eq8 (M.op (M.op x x) X0) x x X3
       grind)
    | exact superpose eq8 eq26
    | exact resolve eq26 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq28 X0 X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq28
    | exact resolve eq28 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact superpose eq28 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (M.op X1 X1)) = (M.op X2 (M.op (M.op X3 X4) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 X3 X4
       have i₂ := eq42 X1 X0
       grind)
    | exact superpose eq42 eq8
    | exact resolve eq8 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X0)) = X0 ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X4 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X4 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq117 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq166 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op (M.op X2 X3) (M.op (M.op X4 X5) X0))) = (M.op X6 (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq21 X1 X2 X3 (M.op (M.op X4 X5) X0) X6 x x
       have i₂ := eq8 X0 (M.op x x) X4 X5
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq204 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op X2 X3) (M.op (M.op X4 X5) X0)) = (M.op X6 (M.op X0 X0)) := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq166 X0 x X2 X3 X4 X5 X6
       have i₂ := eq29 (M.op X2 X3) X4 X5 X0 x
       grind)
    | exact superpose eq29 eq166
    | exact resolve eq166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq166
  have eq2441 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2476 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2441 (σ X0)
       grind)
    | exact superpose eq2441 eq13
    | exact resolve eq13 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0 X0
       have i₂ := eq2441 (τ X0)
       grind)
    | exact superpose eq2441 eq117
    | exact resolve eq117 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2481 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2478 X0
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq2478
    | exact resolve eq2478 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq2483 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2476 X0
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq2476
    | exact resolve eq2476 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441 eq2476
  have eq2971 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ X0) x
       have i₂ := eq2481 X0
       grind)
    | exact superpose eq2481 eq28
    | exact resolve eq28 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481
  have eq3089 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) x
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq28
    | exact resolve eq28 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3346 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3518 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3346
    | (have j0 := eq3346 X0 X1
       grind)
    | exact resolve eq3346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq4542 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (M.op x x) x x
       have i₂ := eq204 X1 x x x x X0
       grind)
    | (have i₁ := eq53 (M.op x x) X1 x x x
       have i₂ := eq204 (M.op x x) X2 x x x x
       grind)
    | exact superpose eq204 eq53
    | exact resolve eq53 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq204
  have eq7087 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4542 X1 (σ X0) X2
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq4542
    | exact resolve eq4542 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7160 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4542 X1 X2 (σ X0)
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq4542
    | exact resolve eq4542 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542
  have eq7758 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X1 (τ (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2971 (σ X1) X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq2971
    | (have j1 := eq72 X2 X0
       grind)
    | exact resolve eq2971 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2971
  have eq7891 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7758 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7758
    | (have j0 := eq7758 X0 X1 X2
       grind)
    | exact resolve eq7758 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq8331 : ∀ X0 X3 X4 : G, (σ X0) = (M.op X3 (σ X0)) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3089 (M.op (M.op x X3) X0) x
       have i₂ := eq68 X0 (M.op (M.op x X3) X0) x X3 X4
       grind)
    | exact superpose eq68 eq3089
    | (have j1 := eq68 X0 x x X3 X4
       grind)
    | exact resolve eq3089 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3089
  have eq38701 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7160 X2 X1 (σ X0)
       have i₂ := eq2483 X0
       grind)
    | exact superpose eq2483 eq7160
    | exact resolve eq7160 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483 eq7160
  have eq39388 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (k X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38701 X0 X1 X2
       have i₂ := eq13 X0 (M.op X2 X2)
       grind)
    | exact superpose eq13 eq38701
    | exact resolve eq38701 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38701
  have eq168917 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 x
       have i₂ := eq3518 X0 X1
       grind)
    | exact superpose eq3518 eq28
    | (have j1 := eq3518 X2 X0
       grind)
    | exact resolve eq28 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3518
  have eq209793 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq8331 y (σ x) X0
       grind)
    | exact superpose eq8331 eq14
    | (have j1 := eq8331 y x X0
       grind)
    | exact resolve eq14 eq8331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331
  have eq328534 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq7891 y X0 x
       grind)
    | exact superpose eq7891 eq14
    | (have j1 := eq7891 y X0 x
       grind)
    | exact resolve eq14 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891
  have eq328598 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq328534 X0
       have j1 := eq168917 y X0 x
       grind)
    | (have r₁ := eq328534 X0
       have r₂ := eq168917 y x x
       grind)
    | exact resolve eq328534 eq168917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168917 eq328534
  have eq328878 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq7087 X0 X1 y
       have i₂ := eq328598 y
       grind)
    | exact superpose eq328598 eq7087
    | exact resolve eq7087 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087
  have eq329052 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = (σ (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq39388 X1 X0 y
       have i₂ := eq328598 y
       grind)
    | exact superpose eq328598 eq39388
    | exact resolve eq39388 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39388
  have eq329548 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq209793 X0
       have i₂ := eq328598 x
       grind)
    | exact superpose eq328598 eq209793
    | (have j0 := eq209793 X0
       grind)
    | exact resolve eq209793 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209793
  have eq329553 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq329548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329548
  have eq329559 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq329553 X0
       have i₂ := eq328598 X0
       grind)
    | exact superpose eq328598 eq329553
    | exact resolve eq329553 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329553
  have eq329783 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq328878 X0 x
       have i₂ := eq329052 x X0
       grind)
    | exact superpose eq329052 eq328878
    | exact resolve eq328878 eq329052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328878 eq329052
  have eq329986 : ∀ X0 : G, y = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq329783 X0
       have i₂ := eq329559 (σ X0)
       grind)
    | exact superpose eq329559 eq329783
    | exact resolve eq329783 eq329559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329783
  have eq330101 : y = (σ y) := by
    first
    | (have i₁ := eq329986 x
       have i₂ := eq329559 x
       grind)
    | exact superpose eq329559 eq329986
    | exact resolve eq329986 eq329559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329559 eq329986
  have eq330436 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq330101
       grind)
    | exact superpose eq330101 eq14
    | exact resolve eq14 eq330101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330575 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq330436
       have i₂ := eq328598 (σ x)
       grind)
    | exact superpose eq328598 eq330436
    | exact resolve eq330436 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330436
  have eq330627 : y ≠ (σ y) := by
    first
    | (have i₁ := eq330575
       have i₂ := eq328598 x
       grind)
    | exact superpose eq328598 eq330575
    | exact resolve eq330575 eq328598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328598 eq330575
  have eq330669 : False := by grind
  exact eq330669

/-- `Equation3546`: `x ◇ y = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation3546 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3546 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3546.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq92 (σ X1) (σ X0)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X1 X0
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1516 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1538 : False := by grind
  exact eq1538

/-- `Equation3566`: `x ◇ y = y ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3566 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3566 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3566.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X1) X3 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 X1 X2 X3
       have i₂ := eq8 X1 X3 X0
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X2 X1) X0) ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X1) X2
       have i₂ := eq12 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op (M.op X2 X0) X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X2 X1) X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq46 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq20 X0 X1 (M.op x x) X4
       have i₂ := eq20 x X0 x X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op x x)
       have i₂ := eq20 x X0 x X1
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) (M.op X0 (M.op (M.op X1 X2) X0))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq53
    | exact resolve eq53 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq60 : ∀ X0 X2 : G, (M.op X2 X0) = (k (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq56 x X0 x
       have i₂ := eq46 X0 x x
       grind)
    | exact superpose eq46 eq56
    | exact resolve eq56 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq88 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq29 (τ X1) X0
       grind)
    | exact superpose eq29 eq17
    | (have j1 := eq29 (τ X1) X0
       grind)
    | exact resolve eq17 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq95 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq51 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq51
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op X2 (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq30 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq150 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ X1) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X0 X1 X2
       have i₂ := eq51 (σ X1) X2
       grind)
    | exact superpose eq51 eq147
    | (have j0 := eq147 X0 X1 X2
       grind)
    | exact resolve eq147 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq266 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (σ X0) (σ X1) X2
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq46
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq46 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq316 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq40
  have eq334 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq316 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq316
    | exact resolve eq316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq356 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 X0)) ∨ (M.op X0 X1) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 x X1 X0
       have i₂ := eq46 X0 X1 x
       grind)
    | exact superpose eq46 eq31
    | exact resolve eq31 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq428 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X2 X0) X1) ∨ (M.op X0 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq356 X0 X1 X2
       have i₂ := eq51 X2 X0
       grind)
    | exact superpose eq51 eq356
    | (have j0 := eq356 X0 X1 X2
       grind)
    | exact resolve eq356 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq551 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X2 X0) = (k (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (M.op X2 X0) X1
       have i₂ := eq46 X2 X0 X1
       grind)
    | exact superpose eq46 eq91
    | (have j0 := eq91 (M.op X2 X0) X1
       grind)
    | (have r₁ := eq91 (M.op x x) x
       have r₂ := eq46 x x x
       grind)
    | exact resolve eq91 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq60 X0 x
       have i₂ := eq12 X0 (M.op x X0)
       grind)
    | exact superpose eq12 eq60
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0
       have i₂ := eq849 X0 X1
       grind)
    | exact superpose eq849 eq95
    | (have j0 := eq95 X0 X1
       have j1 := eq849 X0 X1
       grind)
    | exact resolve eq95 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1169 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1529 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1613 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1529
    | (have j0 := eq1529 X0 X1
       grind)
    | exact resolve eq1529 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1737 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1781 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1737 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1737
    | (have j0 := eq1737 X0 X1
       grind)
    | exact resolve eq1737 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq2759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq266
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq266 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2760 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1169 y x
       grind)
    | exact superpose eq1169 eq266
    | (have j1 := eq1169 y x
       grind)
    | exact resolve eq266 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1781 y x
       grind)
    | exact superpose eq1781 eq266
    | (have j1 := eq1781 y x
       grind)
    | (have r₁ := eq266
       have r₂ := eq1781 y x
       grind)
    | exact resolve eq266 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq2762 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq266
       have i₂ := eq1613 y x
       grind)
    | exact superpose eq1613 eq266
    | (have j1 := eq1613 (σ y) (σ x)
       grind)
    | (have r₁ := eq266
       have r₂ := eq1613 y x
       grind)
    | exact resolve eq266 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq1613
  have eq2763 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2762
  have eq2764 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2761
  have eq2765 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2760
  have eq2766 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2759
  have eq2781 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq334 x
       have i₂ := eq2763
       grind)
    | exact superpose eq2763 eq334
    | exact resolve eq334 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2811 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2781
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2781
    | exact resolve eq2781 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq2903 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2811
       grind)
    | exact superpose eq2811 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq2911 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2903
  have eq3057 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq46 x y X0
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq46
    | exact resolve eq46 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq5406 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq150 x y X0
       grind)
    | exact superpose eq150 eq14
    | (have j1 := eq150 x y X0
       grind)
    | exact resolve eq14 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq8893 : y = (k y (M.op x y)) ∨ y = (M.op x x) := by grind
  have eq22788 : y = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8893
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq8893
    | exact resolve eq8893 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911 eq8893
  have eq22817 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq22788
  have eq33484 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq334 x
       have i₂ := eq2764
       grind)
    | exact superpose eq2764 eq334
    | exact resolve eq334 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq2764
  have eq33566 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq33484
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33484
    | exact resolve eq33484 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33484
  have eq33567 : x = (k x y) := by grind
  clear eq33566
  have eq42867 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq551 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq42920 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42867 (σ x)
       have i₂ := eq2766
       grind)
    | exact superpose eq2766 eq42867
    | exact resolve eq42867 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq43009 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42920
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq42920
    | exact resolve eq42920 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42920
  have eq43680 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq43009
       grind)
    | exact superpose eq43009 eq9
    | exact resolve eq9 eq43009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43009
  have eq43730 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43680
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq43680
    | exact resolve eq43680 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43680
  have eq45305 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq60 (σ x) (σ x)
       have i₂ := eq2765
       grind)
    | exact superpose eq2765 eq60
    | exact resolve eq60 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq2765
  have eq45330 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45305
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq45305
    | exact resolve eq45305 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45305
  have eq45502 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq45330
       grind)
    | exact superpose eq45330 eq9
    | exact resolve eq9 eq45330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45330
  have eq45553 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45502
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq45502
    | exact resolve eq45502 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45502
  have eq45556 : y = (k y y) := by
    first
    | (have j1 := eq91 y y
       grind)
    | (have r₁ := eq45553
       have r₂ := eq91 y y
       grind)
    | exact resolve eq45553 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq45553
  have eq45653 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq290 y
       have i₂ := eq45556
       grind)
    | exact superpose eq45556 eq290
    | (have j0 := eq290 y
       grind)
    | exact resolve eq290 eq45556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq45675 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1169 y y
       have i₂ := eq45556
       grind)
    | exact superpose eq45556 eq1169
    | (have j0 := eq1169 y x
       grind)
    | exact resolve eq1169 eq45556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq45556
  have eq45677 : y = (M.op y y) := by grind
  clear eq45675
  have eq45683 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq45653
  have eq45773 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq428 y x y
       have i₂ := eq45677
       grind)
    | exact superpose eq45677 eq428
    | exact resolve eq428 eq45677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq45677
  have eq47393 : y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq22817
       have i₂ := eq45773 x
       grind)
    | exact superpose eq45773 eq22817
    | (have j1 := eq45773 x
       grind)
    | exact resolve eq22817 eq45773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22817
  have eq47398 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq43730
       have i₂ := eq45773 x
       grind)
    | exact superpose eq45773 eq43730
    | (have j1 := eq45773 x
       grind)
    | exact resolve eq43730 eq45773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43730 eq45773
  have eq47466 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq47398
  have eq47469 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq47393
  have eq47635 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq47466
       grind)
    | exact superpose eq47466 eq51
    | exact resolve eq51 eq47466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq47466
  have eq47670 : y = (M.op x y) := by grind
  clear eq47635
  have eq47790 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3057 x
       have i₂ := eq47469
       grind)
    | exact superpose eq47469 eq3057
    | exact resolve eq3057 eq47469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq47469
  have eq47835 : y = (M.op x x) := by grind
  clear eq47790
  have eq47952 : y = (k y x) := by
    first
    | (have i₁ := eq42867 x
       have i₂ := eq47835
       grind)
    | exact superpose eq47835 eq42867
    | exact resolve eq42867 eq47835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42867 eq47835
  have eq48198 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq5406 X0
       have i₂ := eq33567
       grind)
    | exact superpose eq33567 eq5406
    | (have j0 := eq5406 X0
       grind)
    | exact resolve eq5406 eq33567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406 eq33567
  have eq48220 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq48198 X0
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq48198
    | (have j0 := eq48198 X0
       grind)
    | exact resolve eq48198 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48198
  have eq48739 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq272 y x X0
       have i₂ := eq47952
       grind)
    | exact superpose eq47952 eq272
    | (have j0 := eq272 y x x
       grind)
    | exact resolve eq272 eq47952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq47952
  have eq48789 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq48739 X0
       have i₂ := eq45683
       grind)
    | exact superpose eq45683 eq48739
    | (have j0 := eq48739 X0
       grind)
    | exact resolve eq48739 eq45683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48739
  have eq48802 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq48789 X0
       have j1 := eq48220 X0
       grind)
    | (have r₁ := eq48789 X0
       have r₂ := eq48220 X0
       grind)
    | exact resolve eq48789 eq48220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48220 eq48789
  have eq48859 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45683
       have i₂ := eq48802 (σ y)
       grind)
    | exact superpose eq48802 eq45683
    | exact resolve eq45683 eq48802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45683 eq48802
  have eq49143 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq48859
       grind)
    | exact superpose eq48859 eq14
    | exact resolve eq14 eq48859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48859
  have eq49253 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq49143
       have i₂ := eq47670
       grind)
    | exact superpose eq47670 eq49143
    | exact resolve eq49143 eq47670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47670 eq49143
  have eq49254 : False := by grind
  exact eq49254

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation3583 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op (M.op X0 X0) X1) X2
       grind)
    | (have r₁ := eq11 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq8 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq24 X1 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq53 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq153 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq168 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq167
    | exact resolve eq167 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq167
  have eq213 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) (σ X0) x
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq20
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq20 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq292 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq338 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq292 (σ X0)
       grind)
    | exact superpose eq292 eq53
    | exact resolve eq53 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq292
  have eq341 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq338
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq470 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X0 X1)
       have i₂ := eq168 X0 X1
       grind)
    | exact superpose eq168 eq215
    | (have j0 := eq215 (M.op X0 X1)
       grind)
    | exact resolve eq215 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq215
  have eq475 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq489 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq489
    | (have j0 := eq489 X0 X1
       grind)
    | exact resolve eq489 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq691 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq213 y x X0
       grind)
    | exact superpose eq213 eq14
    | (have j1 := eq213 y x X0
       grind)
    | exact resolve eq14 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X1 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq758 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq20
    | exact resolve eq20 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq4109 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 (τ X0) (τ X1)
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq707
    | (have j0 := eq707 (τ X0) (τ X1)
       grind)
    | exact resolve eq707 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq707
  have eq4130 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4109 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4109
    | (have j0 := eq4109 X0 X1
       grind)
    | exact resolve eq4109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4139 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4130 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4130
    | (have j0 := eq4130 X0 X1
       grind)
    | exact resolve eq4130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq4143 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4139
    | (have j0 := eq4139 X0 X1
       grind)
    | exact resolve eq4139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4144 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4143 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4143
    | (have j0 := eq4143 X0 X1
       grind)
    | exact resolve eq4143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4657 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq524 x y
       grind)
    | exact superpose eq524 eq691
    | (have j0 := eq691 X0
       have j1 := eq524 x y
       grind)
    | (have r₁ := eq691 X0
       have r₂ := eq524 x y
       grind)
    | exact resolve eq691 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq691
  have eq4658 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq5061 : y = (k y (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq341 y
       have i₂ := eq4658 (σ y)
       grind)
    | exact superpose eq4658 eq341
    | exact resolve eq341 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq4658
  have eq5067 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5061
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq5061
    | exact resolve eq5061 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5061
  have eq5162 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4144 y y
       have i₂ := eq5067
       grind)
    | exact superpose eq5067 eq4144
    | (have j0 := eq4144 y y
       grind)
    | (have r₁ := eq4144 y y
       have r₂ := eq5067
       grind)
    | exact resolve eq4144 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq5067
  have eq5163 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq5162
  have eq5327 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20 y y x
       have i₂ := eq5163
       grind)
    | exact superpose eq5163 eq20
    | exact resolve eq20 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163
  have eq5476 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq20 y x x
       have i₂ := eq5327 X0
       grind)
    | exact superpose eq5327 eq20
    | (have j1 := eq5327 X0
       grind)
    | exact resolve eq20 eq5327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5327
  have eq5819 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5476 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5820 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5819
  have eq5853 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq758 x y x
       have i₂ := eq5820 x
       grind)
    | exact superpose eq5820 eq758
    | exact resolve eq758 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq6150 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5853 (σ x)
       grind)
    | exact superpose eq5853 eq14
    | exact resolve eq14 eq5853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5853
  have eq6155 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6150
       have i₂ := eq5820 x
       grind)
    | exact superpose eq5820 eq6150
    | exact resolve eq6150 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5820 eq6150
  have eq6156 : False := by grind
  exact eq6156

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation3587 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq18 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq20 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X1)
       have r₂ := eq25 X0 X1
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq46 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 x (M.op X0 X1)
       have i₂ := eq20 X0 X1 x
       grind)
    | exact superpose eq20 eq44
    | exact resolve eq44 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq85 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X1) (σ X0) x
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq20
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq20 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq141 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (M.op X1 (σ X0))
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq64
    | exact resolve eq64 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq64
  have eq153 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq141
    | exact resolve eq141 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq395 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (M.op X0 X1)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq124
    | (have j0 := eq124 (M.op X0 X1)
       grind)
    | exact resolve eq124 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq124
  have eq400 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq414 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq450 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq414
    | (have j0 := eq414 X0 X1
       grind)
    | exact resolve eq414 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq613 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq121 y x X0
       grind)
    | exact superpose eq121 eq14
    | (have j1 := eq121 y x X0
       grind)
    | exact resolve eq14 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq121 X1 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1431 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq400 X0 X1
       grind)
    | exact superpose eq400 eq20
    | exact resolve eq20 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq3346 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq626 (τ X0) (τ X1)
       have i₂ := eq85 X1 X0
       grind)
    | exact superpose eq85 eq626
    | (have j0 := eq626 (τ X0) (τ X1)
       grind)
    | exact resolve eq626 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq626
  have eq3365 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3346 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3346
    | (have j0 := eq3346 X0 X1
       grind)
    | exact resolve eq3346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3372 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3365 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3365
    | (have j0 := eq3365 X0 X1
       grind)
    | exact resolve eq3365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3376 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3372 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3372
    | (have j0 := eq3372 X0 X1
       grind)
    | exact resolve eq3372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq3377 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3376
    | (have j0 := eq3376 X0 X1
       grind)
    | exact resolve eq3376 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3871 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq613 X0
       have i₂ := eq450 x y
       grind)
    | exact superpose eq450 eq613
    | (have j0 := eq613 X0
       have j1 := eq450 x y
       grind)
    | (have r₁ := eq613 X0
       have r₂ := eq450 x y
       grind)
    | exact resolve eq613 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq613
  have eq3872 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq4360 : y = (k y (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq153 y x
       have i₂ := eq3872 x
       grind)
    | exact superpose eq3872 eq153
    | exact resolve eq153 eq3872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3872
  have eq4391 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4360
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4360
    | exact resolve eq4360 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4552 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3377 y y
       have i₂ := eq4391
       grind)
    | exact superpose eq4391 eq3377
    | (have j0 := eq3377 y y
       grind)
    | (have r₁ := eq3377 y y
       have r₂ := eq4391
       grind)
    | exact resolve eq3377 eq4391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377 eq4391
  have eq4553 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq4552
  have eq4651 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq20 y y x
       have i₂ := eq4553
       grind)
    | exact superpose eq4553 eq20
    | exact resolve eq20 eq4553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553
  have eq4695 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq20 y x x
       have i₂ := eq4651 X0
       grind)
    | exact superpose eq4651 eq20
    | (have j1 := eq4651 X0
       grind)
    | exact resolve eq20 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4651
  have eq4859 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4695 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4860 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq4859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4945 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1431 x y x
       have i₂ := eq4860 x
       grind)
    | exact superpose eq4860 eq1431
    | exact resolve eq1431 eq4860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq5245 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4945 (σ x)
       grind)
    | exact superpose eq4945 eq14
    | exact resolve eq14 eq4945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4945
  have eq5255 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5245
       have i₂ := eq4860 x
       grind)
    | exact superpose eq4860 eq5245
    | exact resolve eq5245 eq4860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860 eq5245
  have eq5256 : False := by grind
  exact eq5256

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pyx_Equation3591 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq8 X0 X1 (M.op X2 X3)
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
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq47 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq67 : ∀ X0 X1 X2 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq47 X0 (σ X1) X2
       grind)
    | exact superpose eq47 eq28
    | (have j1 := eq47 (τ X0) X1 X2
       grind)
    | exact resolve eq28 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 (τ X1) X2
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 (σ X0) X1 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq47 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq47 X0 X2 (τ X1)
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 X0 X2 X2
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X2 X0 X1
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq21
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op (M.op X4 X0) X5) X2) (M.op (M.op X4 X5) X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1) X2 X3
       have i₂ := eq21 X4 X5 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq8 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq91 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 (M.op X0 X1) X3 X2 (M.op (M.op X4 X0) X5) (M.op (M.op X4 X5) X1)
       grind)
    | exact superpose eq93 eq91
    | exact resolve eq91 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 X0 X1 X2 X3
       have i₂ := eq96 X2 X1 X0 X2
       grind)
    | exact superpose eq96 eq84
    | (have j0 := eq84 X0 X1 X2 X3
       grind)
    | exact resolve eq84 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X0 X1 X2 X3 x x
       have i₂ := eq21 x x X0 X1
       grind)
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq21 X2 X3 X0 X1
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq22 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq144 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq93 eq144
    | exact resolve eq144 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X0 X1 X2 X3 X4 x
       have i₂ := eq98 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq98 eq141
    | exact resolve eq141 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq141
  have eq157 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq129 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq93 eq129
    | exact resolve eq129 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq173 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq68 X0 (σ X1) X2
       grind)
    | exact superpose eq68 eq13
    | (have j1 := eq68 X0 X1 X2
       grind)
    | exact resolve eq13 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq224 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (σ X0) X1 X2
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq289 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq957 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X1 (σ X0) X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq74
    | (have j0 := eq74 X1 X1 X2
       grind)
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1036 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq957
    | (have j0 := eq957 X0 X1 X2
       grind)
    | exact resolve eq957 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1282 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1036 X2 X0 (τ X1)
       grind)
    | exact superpose eq1036 eq15
    | (have j1 := eq1036 X2 X0 X2
       grind)
    | exact resolve eq15 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq1036
  have eq1323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) (M.op X3 X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 X4 X2 (M.op (M.op X0 X2) X1)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq96
    | exact resolve eq96 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2 (M.op X0 X1)
       have i₂ := eq96 X1 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1358 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 (M.op X3 X1) X4 (M.op X3 X0) X2
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op (M.op X3 X0) X2) (M.op (M.op X0 (M.op X1 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X3 X1) X4 (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq8
    | exact resolve eq8 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op (M.op X3 X1) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq22 X4 X5 (M.op X3 X1) (M.op (M.op X3 X0) X2)
       have i₂ := eq96 X1 X2 X3 X0
       grind)
    | exact superpose eq96 eq22
    | exact resolve eq22 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1372 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1363 X0 X1 X2 X3 X4 X5
       have i₂ := eq157 X1 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq157 eq1363
    | exact resolve eq1363 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1375 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1360 X0 X1 X2 X3 X4
       have i₂ := eq93 (M.op X0 (M.op X1 X2)) X4 X0 X3 X2
       grind)
    | exact superpose eq93 eq1360
    | exact resolve eq1360 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X1) X4)) = (M.op X3 (M.op (M.op X0 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1358 X0 X1 X2 X3 X4
       have i₂ := eq157 X0 X1 X2 X3 X0 X4
       grind)
    | exact superpose eq157 eq1358
    | exact resolve eq1358 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq1358
  have eq1392 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 (M.op X0 X1)) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1323 X0 X1 X2 X3 X4
       have i₂ := eq93 X3 X4 X2 X0 X1
       grind)
    | exact superpose eq93 eq1323
    | exact resolve eq1323 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))) X5)) = (M.op X0 (M.op (M.op X4 (M.op X3 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1372 X0 X1 X2 X3 X4 X5
       have i₂ := eq93 X4 X5 X0 X3 X2
       grind)
    | exact superpose eq93 eq1372
    | exact resolve eq1372 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1372
  have eq1400 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X0 (M.op (M.op (M.op X2 X1) (M.op X0 (M.op X3 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1375 X0 X1 X2 X3 X4
       have i₂ := eq150 X2 X0 (M.op X3 X2) X1 X4
       grind)
    | (have i₁ := eq1375 X0 X1 X2 X1 X4
       have i₂ := eq150 X0 X1 X2 (M.op X1 X2) X4
       grind)
    | exact superpose eq150 eq1375
    | exact resolve eq1375 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1410 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op (M.op X3 X2) (M.op (M.op X2 X1) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1400 x X1 X2 X3 X4
       have i₂ := eq22 (M.op X2 X1) X4 x (M.op X3 X2)
       grind)
    | exact superpose eq22 eq1400
    | exact resolve eq1400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1415 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X4) = (M.op X3 (M.op (M.op X2 (M.op X2 X1)) X4)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1410 X1 X2 X3 X4
       have i₂ := eq1392 X2 X1 X3 X2 X4
       grind)
    | (have i₁ := eq1410 (M.op x X1) X3 X3 X4
       have i₂ := eq1392 x X1 (M.op X3 X3) X3 X4
       grind)
    | exact superpose eq1392 eq1410
    | exact resolve eq1410 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1423 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1357 X3 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq22 X1 X2 X3 X0
       grind)
    | exact superpose eq22 eq1357
    | exact resolve eq1357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X3) X1)) = (M.op (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1357 X2 X3 (M.op (M.op X0 X3) X1)
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq1357
    | exact resolve eq1357 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X0 X2) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 X2 (M.op X3 X1)
       have i₂ := eq1357 X0 X3 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X0 X1) X0
       have i₂ := eq1357 X2 X0 X1
       grind)
    | exact superpose eq1357 eq8
    | exact resolve eq8 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X2 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op X0 X1) X3 X1 X2
       have i₂ := eq1357 X0 X1 X2
       grind)
    | exact superpose eq1357 eq22
    | exact resolve eq22 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1458 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op x x)
       have i₂ := eq1357 x x x
       grind)
    | exact superpose eq1357 eq11
    | (have r₁ := eq11 X0 (M.op x x)
       have r₂ := eq1357 x x x
       grind)
    | exact resolve eq11 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op X0 X2) X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 (M.op X0 X2) X4 (M.op X2 X1) X3
       have i₂ := eq1357 X0 X2 X1
       grind)
    | exact superpose eq1357 eq21
    | exact resolve eq21 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1475 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X2 (M.op (M.op X0 X1) X4)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1461 X0 X1 X2 X3 X4
       have i₂ := eq135 X2 (M.op (M.op X0 X1) X4) X0 X4 X3
       grind)
    | (have i₁ := eq1461 X0 X1 X2 X4 X1
       have i₂ := eq135 (M.op X0 X2) X1 (M.op X0 X1) X1 X4
       grind)
    | exact superpose eq135 eq1461
    | exact resolve eq1461 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq1461
  have eq1479 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X0 (M.op (M.op (M.op X0 X2) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 X0 X1 (M.op (M.op X0 X2) X3)
       grind)
    | (have i₁ := eq1452 X0 X1 X2 X3
       have i₂ := eq1454 (M.op (M.op X0 X2) X3) X1 X0
       grind)
    | exact superpose eq1454 eq1452
    | exact resolve eq1452 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1454
  have eq1492 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) (M.op X0 (M.op X1 X2)) X2 X4
       grind)
    | (have i₁ := eq1423 X0 X1 X2 X3 X4
       have i₂ := eq1457 (M.op X1 (M.op X3 X0)) X2 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq1457 eq1423
    | exact resolve eq1423 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1498 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X4) (M.op (M.op X4 (M.op X0 X1)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1475 X0 X1 X2 X3 X4
       have i₂ := eq148 X4 X2 X3 (M.op X0 X4) X0 X1
       grind)
    | (have i₁ := eq1475 X0 X1 X0 (M.op X1 X2) x
       have i₂ := eq148 X0 X1 X2 (M.op X0 x) (M.op X0 X1) x
       grind)
    | exact superpose eq148 eq1475
    | exact resolve eq1475 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1508 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X1 (M.op X0 (M.op X1 X2)))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1492 X0 X1 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 (M.op X1 X2)) X3 X4
       grind)
    | (have i₁ := eq1492 X1 X0 X2 X3 X4
       have i₂ := eq150 X0 X1 (M.op X0 X2) (M.op X3 X1) X4
       grind)
    | exact superpose eq150 eq1492
    | exact resolve eq1492 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq1492
  have eq1512 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) X3) = (M.op X0 (M.op (M.op X4 (M.op X4 (M.op X0 X1))) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1498 X0 X1 X2 X3 X4
       have i₂ := eq1392 X4 (M.op X0 X1) X0 X4 (M.op X2 X3)
       grind)
    | (have i₁ := eq1498 X0 X1 X2 X3 X3
       have i₂ := eq1392 X0 X1 (M.op X0 X3) X3 (M.op X2 X3)
       grind)
    | exact superpose eq1392 eq1498
    | exact resolve eq1498 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1498
  have eq1516 : ∀ X0 X2 X3 X4 : G, (M.op X3 X4) = (M.op X0 (M.op (M.op (M.op X0 X3) (M.op X2 X2)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1508 X0 x X2 X3 X4
       have i₂ := eq1397 X0 x X2 X2 (M.op X0 X3) X4
       grind)
    | exact superpose eq1397 eq1508
    | exact resolve eq1508 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397 eq1508
  have eq1518 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1512 X0 X1 X2 X3 x
       have i₂ := eq1377 x X0 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq1377 eq1512
    | exact resolve eq1512 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377 eq1512
  have eq1521 : ∀ X2 X3 X4 : G, (M.op X3 X4) = (M.op X3 (M.op (M.op X2 X2) X4)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1516 x X2 X3 X4
       have i₂ := eq1479 x X4 X3 (M.op X2 X2)
       grind)
    | exact superpose eq1479 eq1516
    | exact resolve eq1516 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq1516
  have eq1523 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1518 X0 X1 X2 X3
       have i₂ := eq1435 X2 X3 X0 X0
       grind)
    | (have i₁ := eq1518 X0 X1 (M.op X0 X3) X1
       have i₂ := eq1435 X0 X1 (M.op X0 X0) X3
       grind)
    | exact superpose eq1435 eq1518
    | exact resolve eq1518 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1518
  have eq1525 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X2 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1523 x X1 X2 X3
       have i₂ := eq8 X2 X3 x
       grind)
    | exact superpose eq8 eq1523
    | exact resolve eq1523 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X2 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)
       have i₂ := eq110 X3 X4 X0 X1
       grind)
    | exact superpose eq110 eq8
    | exact resolve eq8 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X1 X2
       grind)
    | (have i₁ := eq1572 X0 X1 X2 X3 X4
       have i₂ := eq1457 X0 X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) X1) X2
       grind)
    | exact superpose eq1457 eq1572
    | exact resolve eq1572 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1650 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X1 (M.op (M.op X3 X4) (M.op X3 X4))) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X0 X1 X2 X3 X4
       have i₂ := eq148 X1 X0 X2 X1 (M.op X3 X4) (M.op X3 X4)
       grind)
    | (have i₁ := eq1612 X0 x (M.op X1 X2) X3 X4
       have i₂ := eq148 X0 X1 X2 x (M.op (M.op X3 X4) (M.op X3 X4)) x
       grind)
    | exact superpose eq148 eq1612
    | exact resolve eq1612 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1681 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X3 X4) (M.op X3 X4)) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1650 X0 X1 X2 X3 X4
       have i₂ := eq148 (M.op X3 X4) X1 (M.op X0 X2) X1 X3 X4
       grind)
    | (have i₁ := eq1650 X1 X0 X2 X3 X4
       have i₂ := eq148 X0 X1 X2 X0 (M.op X3 X4) (M.op X3 X4)
       grind)
    | exact superpose eq148 eq1650
    | exact resolve eq1650 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1650
  have eq1707 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1681 X0 X1 X2 x x
       have i₂ := eq1521 (M.op x x) X1 (M.op X1 (M.op X0 X2))
       grind)
    | (have i₁ := eq1681 X0 x X2 x x
       have i₂ := eq1521 X2 x (M.op (M.op (M.op x x) (M.op x x)) (M.op x (M.op X0 X2)))
       grind)
    | exact superpose eq1521 eq1681
    | exact resolve eq1681 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq1681
  have eq1869 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (M.op X0 X0)
       have i₂ := eq1470 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1470 eq289
    | (have j0 := eq289 (M.op X0 X0)
       grind)
    | exact resolve eq289 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1879 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq289
    | (have j0 := eq289 (τ X0)
       grind)
    | exact resolve eq289 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq289
  have eq1887 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1879 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1879
    | (have j0 := eq1879 X0
       grind)
    | exact resolve eq1879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1901 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1893 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1893
    | (have j0 := eq1893 X0
       grind)
    | exact resolve eq1893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2070 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1707 X1 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1707
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq1707 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq109 X1 X1 X2 X3
       grind)
    | exact superpose eq109 eq11
    | (have j1 := eq109 X1 X1 X2 X3
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq2387 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (k X2 X1) ∨ (M.op X1 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq2245 X0 X1 X2 X3
       have j1 := eq2070 X1 X1 X3
       grind)
    | (have r₁ := eq2245 X1 X0 X2 X3
       have r₂ := eq2070 X0 X1 X2
       grind)
    | exact resolve eq2245 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq2245
  have eq4508 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq72 x y X0
       grind)
    | exact superpose eq72 eq14
    | (have j1 := eq72 x x X0
       grind)
    | exact resolve eq14 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq4588 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq4508 X0
       have j1 := eq1282 x X0 x
       grind)
    | (have r₁ := eq4508 X0
       have r₂ := eq1282 x x y
       grind)
    | exact resolve eq4508 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq4508
  have eq4631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1901 (σ x)
       have i₂ := eq4588 (σ x)
       grind)
    | exact superpose eq4588 eq1901
    | (have j0 := eq1901 (σ x)
       grind)
    | (have r₁ := eq1901 (σ x)
       have r₂ := eq4588 (σ x)
       grind)
    | exact resolve eq1901 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4648 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq4588 (σ X0)
       grind)
    | exact superpose eq4588 eq28
    | exact resolve eq28 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4588
  have eq4653 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4631
  have eq4654 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq4648 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq4648
    | exact resolve eq4648 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4805 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1901 x
       have i₂ := eq4654 x
       grind)
    | exact superpose eq4654 eq1901
    | (have j0 := eq1901 x
       grind)
    | (have r₁ := eq1901 x
       have r₂ := eq4654 x
       grind)
    | exact resolve eq1901 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq4654
  have eq4824 : x = (M.op x x) := by grind
  clear eq4805
  have eq4844 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 x X1 x X0
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq21
    | exact resolve eq21 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4859 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1707 x x x
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq1707
    | exact resolve eq1707 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4869 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x (M.op x X1) X1 X0
       grind)
    | (have i₁ := eq4844 X0 X1
       have i₂ := eq1457 x X1 (M.op x X1) X0
       grind)
    | exact superpose eq1457 eq4844
    | exact resolve eq4844 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457 eq4844
  have eq4874 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4869 X0 X1
       have i₂ := eq1415 X1 x X1 X0
       grind)
    | (have i₁ := eq4869 X0 (M.op x X1)
       have i₂ := eq1415 X1 x x (M.op (M.op x (M.op x (M.op x X1))) X0)
       grind)
    | exact superpose eq1415 eq4869
    | exact resolve eq4869 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq4869
  have eq4876 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4874 X0 X1
       have i₂ := eq1525 X1 X1 X0
       grind)
    | exact superpose eq1525 eq4874
    | exact resolve eq4874 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq4874
  have eq9519 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1357 (σ x) (σ x) X0
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1357
    | exact resolve eq1357 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq9524 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1707 (σ x) x (σ x)
       have i₂ := eq4653
       grind)
    | exact superpose eq4653 eq1707
    | exact resolve eq1707 eq4653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq4653
  have eq9527 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq9524 x
       have i₂ := eq4876 (σ x) x
       grind)
    | exact superpose eq4876 eq9524
    | exact resolve eq9524 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9524
  have eq9530 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9519 X0
       have i₂ := eq4876 X0 (σ x)
       grind)
    | exact superpose eq4876 eq9519
    | exact resolve eq9519 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9519
  have eq15951 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9530 (σ y)
       grind)
    | exact superpose eq9530 eq14
    | exact resolve eq14 eq9530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9530
  have eq140067 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4876 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq4876
    | exact resolve eq4876 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140074 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq140067 X0
       have i₂ := eq1887 X0
       grind)
    | exact superpose eq1887 eq140067
    | exact resolve eq140067 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq140067
  have eq145925 : ∀ X0 X1 : G, (σ X0) = (M.op x (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140074 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq140074
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq140074 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140074
  have eq149127 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X2 (M.op X2 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2387 X0 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq149130 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op x X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149127 X0 X1 x
       have i₂ := eq4876 X1 x
       grind)
    | exact superpose eq4876 eq149127
    | (have j0 := eq149127 X0 X1 x
       grind)
    | (have r₁ := eq149127 (M.op X1 (M.op x X1)) X1 x
       have r₂ := eq4876 (M.op x X1) X1
       grind)
    | (have r₁ := eq149127 x x X1
       have r₂ := eq4876 x X1
       grind)
    | exact resolve eq149127 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149127
  have eq156481 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (k (M.op X1 X0) X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149130 (M.op X1 X0) X1
       have i₂ := eq4876 X0 X1
       grind)
    | exact superpose eq4876 eq149130
    | (have r₁ := eq149130 (M.op X0 X0) X0
       have r₂ := eq4876 X0 X0
       grind)
    | exact resolve eq149130 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876 eq149130
  have eq288319 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq156481 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156481
  have eq288673 : ∀ X0 X1 : G, (σ X0) = (σ (M.op x X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (M.op X0 X0) X1
       have i₂ := eq288319 X0
       grind)
    | exact superpose eq288319 eq173
    | (have j0 := eq173 X0 X1 X1
       grind)
    | exact resolve eq173 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq289258 : ∀ X0 : G, (σ y) ≠ (M.op x (σ y)) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15951
       have i₂ := eq288673 y X0
       grind)
    | exact superpose eq288673 eq15951
    | (have j1 := eq288673 y X0
       grind)
    | exact resolve eq15951 eq288673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288673
  have eq289320 : ∀ X0 : G, (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq289258 X0
       have j1 := eq145925 y X0
       grind)
    | (have r₁ := eq289258 X0
       have r₂ := eq145925 y x
       grind)
    | exact resolve eq289258 eq145925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145925 eq289258
  have eq289546 : ∀ X0 X1 : G, y = (M.op y X0) ∨ (k X1 (σ y)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq224 y X0 X1
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq224
    | (have j0 := eq224 y X1 X1
       grind)
    | exact resolve eq224 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq310998 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4859 y
       have i₂ := eq289546 (M.op y x) X0
       grind)
    | exact superpose eq289546 eq4859
    | (have j1 := eq289546 X0 X0
       grind)
    | exact resolve eq4859 eq289546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859 eq289546
  have eq311089 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq310998 (σ X0)
       grind)
    | exact superpose eq310998 eq13
    | exact resolve eq13 eq310998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310998
  have eq311102 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq311089 X0
       have i₂ := eq289320 X0
       grind)
    | exact superpose eq289320 eq311089
    | exact resolve eq311089 eq289320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289320 eq311089
  have eq311186 : (M.op x (σ y)) = (k (σ (M.op y y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq288319 (σ y)
       have i₂ := eq311102 y
       grind)
    | exact superpose eq311102 eq288319
    | exact resolve eq288319 eq311102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311102
  have eq311215 : (M.op x (σ y)) = (σ (k (M.op y y) y)) ∨ x = y := by
    first
    | (have i₁ := eq311186
       have i₂ := eq13 (M.op y y) y
       grind)
    | exact superpose eq13 eq311186
    | exact resolve eq311186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311186
  have eq311245 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq311215
       have i₂ := eq288319 y
       grind)
    | exact superpose eq288319 eq311215
    | exact resolve eq311215 eq288319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288319 eq311215
  have eq311249 : x = y := by
    first
    | (have r₁ := eq311245
       have r₂ := eq15951
       grind)
    | exact resolve eq311245 eq15951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311245
  have eq316079 : (M.op x (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15951
       have i₂ := eq311249
       grind)
    | exact superpose eq311249 eq15951
    | exact resolve eq15951 eq311249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951 eq311249
  have eq316098 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq316079
       have i₂ := eq4824
       grind)
    | exact superpose eq4824 eq316079
    | exact resolve eq316079 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq316079
  have eq316104 : False := by grind
  exact eq316104

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation3600 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq8 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq19 X0 X1 x X3
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1 x
       have i₂ := eq21 X0 X1 x
       grind)
    | exact superpose eq21 eq36
    | (have j0 := eq36 X0 X1 x
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq64 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq69 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq235 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq69
  have eq250 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq235
    | exact resolve eq235 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq406 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) (σ X0) x
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq21
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq21 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq926 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (M.op X0 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq409
    | (have j0 := eq409 (M.op X0 X1)
       grind)
    | exact resolve eq409 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq409
  have eq932 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1065 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1155 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1065
    | (have j0 := eq1065 X0 X1
       grind)
    | exact resolve eq1065 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1678 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq932 X0 X1
       grind)
    | exact superpose eq932 eq21
    | exact resolve eq21 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq2202 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1678 X1 X1 X2
       have i₂ := eq1155 X0 X1
       grind)
    | (have i₁ := eq1678 X0 X1 X2
       have i₂ := eq1155 (M.op X0 X1) X1
       grind)
    | exact superpose eq1155 eq1678
    | (have j1 := eq1155 X0 X1
       grind)
    | exact resolve eq1678 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1678
  have eq2760 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq406 y x X0
       grind)
    | exact superpose eq406 eq14
    | (have j1 := eq406 y x X0
       grind)
    | exact resolve eq14 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq2797 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2760 X0
       have j1 := eq2202 y x X0
       grind)
    | (have r₁ := eq2760 X0
       have r₂ := eq2202 y x x
       grind)
    | exact resolve eq2760 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq2760
  have eq2858 : y = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq250 y
       have i₂ := eq2797 (σ y)
       grind)
    | exact superpose eq2797 eq250
    | exact resolve eq250 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq2860 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2797 (σ x)
       grind)
    | exact superpose eq2797 eq14
    | exact resolve eq14 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2864 : y = (k y y) := by
    first
    | (have i₁ := eq2858
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2858
    | exact resolve eq2858 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2975 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 y y
       have i₂ := eq2864
       grind)
    | exact superpose eq2864 eq41
    | (have j0 := eq41 y y
       grind)
    | exact resolve eq41 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2864
  have eq2978 : y = (M.op y y) := by grind
  clear eq2975
  have eq3174 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq21 y y x
       have i₂ := eq2978
       grind)
    | exact superpose eq2978 eq21
    | exact resolve eq21 eq2978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2978
  have eq3704 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2860
       have i₂ := eq3174 x
       grind)
    | exact superpose eq3174 eq2860
    | exact resolve eq2860 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860 eq3174
  have eq3708 : False := by grind
  exact eq3708
