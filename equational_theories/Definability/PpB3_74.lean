import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
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
  have eq53 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq207 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (M.op X0 x)
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq354 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 X0 X1 x y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq376 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq210 eq354
    | exact resolve eq354 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq391 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq210 eq207
    | exact resolve eq207 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq533 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq534 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq210 eq533
    | exact resolve eq533 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq535 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq534 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq534
    | exact resolve eq534 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq536 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq210 eq535
    | exact resolve eq535 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq559 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq536 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq536 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq660 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq665 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq660 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq667 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq665 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq665 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq689 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq56 X0 X0
       have i₂ := eq560 X0
       grind)
    | exact superpose eq560 eq56
    | exact resolve eq56 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq210 eq689
    | exact resolve eq689 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq4907 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq560 eq667
    | (have j0 := eq667 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq667 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq4922 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq391 eq4907
    | (have j0 := eq4907 X0
       grind)
    | exact resolve eq4907 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq4923 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq4922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922
  have eq4957 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4923 eq244
    | exact resolve eq244 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq4962 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq4923 eq36
    | exact resolve eq36 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq4963 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq4923 eq37
    | exact resolve eq37 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4923
  have eq4986 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq560 eq4963
    | exact resolve eq4963 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq4987 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq560 eq4962
    | exact resolve eq4962 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq5019 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq4986
       grind)
    | exact superpose eq4986 eq16
    | exact resolve eq16 eq4986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4986
  have eq5042 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq4987
       grind)
    | exact superpose eq4987 eq16
    | exact resolve eq16 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4987
  have eq5201 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq560 eq4957
    | exact resolve eq4957 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq5207 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq4957 eq700
    | exact resolve eq700 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq4957
  have eq5284 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5201 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5201
    | exact resolve eq5201 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5564 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq5284 X0
       grind)
    | exact superpose eq5284 eq15
    | exact resolve eq15 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284
  have eq5842 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0) (σ X0)
       have i₂ := eq5564 X0
       grind)
    | exact superpose eq5564 eq56
    | exact resolve eq56 eq5564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5564
  have eq5846 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq210 eq5842
    | exact resolve eq5842 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5842
  have eq6213 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq536 eq5207
    | exact resolve eq5207 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq6244 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq6213
       have i₂ := eq5201 (M.op x sF0)
       grind)
    | exact superpose eq5201 eq6213
    | exact resolve eq6213 eq5201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201 eq6213
  have eq6310 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq536 eq6244
    | exact resolve eq6244 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq6244
  have eq6371 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq6310 eq15
    | exact resolve eq15 eq6310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310
  have eq31615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq31616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq31615
    | exact resolve eq31615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31615
  have eq31627 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq31616
       have r₂ := eq28
       grind)
    | exact resolve eq31616 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31616
  have eq31631 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31627 eq5019
    | exact resolve eq5019 eq31627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5019 eq31627
  have eq31669 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq31631
    | exact resolve eq31631 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31631
  have eq31670 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq31669
  have eq31675 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31670 eq5042
    | exact resolve eq5042 eq31670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042 eq31670
  have eq31709 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq31675
    | exact resolve eq31675 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31675
  have eq31710 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq31709
  have eq31737 : (M.op y y) = (M.op x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq376 y y
       have i₂ := eq31710
       grind)
    | exact superpose eq31710 eq376
    | exact resolve eq376 eq31710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq32233 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31710
       have i₂ := eq31737
       grind)
    | exact superpose eq31737 eq31710
    | exact resolve eq31710 eq31737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31710 eq31737
  have eq32246 : y = (M.op x (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq32233
  have eq32285 : y = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32246 eq6371
    | exact resolve eq6371 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32311 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32246 eq56
    | exact resolve eq56 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32313 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq210 eq32311
    | exact resolve eq32311 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32311
  have eq32322 : y = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32285
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32285
    | exact resolve eq32285 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32285
  have eq32326 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32313
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32313
    | exact resolve eq32313 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32313
  have eq32811 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq5846 x
       have i₂ := eq32322
       grind)
    | exact superpose eq32322 eq5846
    | exact resolve eq5846 eq32322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32816 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq32322
       grind)
    | exact superpose eq32322 eq56
    | exact resolve eq56 eq32322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32322
  have eq32818 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq210 eq32816
    | exact resolve eq32816 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32816
  have eq32823 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32811
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32811
    | exact resolve eq32811 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32811
  have eq32833 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32818
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32818
    | exact resolve eq32818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32818
  have eq32835 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32823
    | exact resolve eq32823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32823
  have eq32839 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq32835
    | exact resolve eq32835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32835
  have eq32942 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32833 eq6371
    | exact resolve eq6371 eq32833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32979 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq21 eq32942
    | exact resolve eq32942 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32942
  have eq33176 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq32839 eq32833
    | exact resolve eq32833 eq32839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32833 eq32839
  have eq33183 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq33176
  have eq33193 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33183 eq28
    | exact resolve eq28 eq33183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33183
  have eq33194 : y = (σ y) := by
    first
    | (have r₁ := eq33193
       have r₂ := eq32979
       grind)
    | exact resolve eq33193 eq32979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32979 eq33193
  have eq33610 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq33194 eq27
    | exact resolve eq27 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq36158 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32326 eq32246
    | exact resolve eq32246 eq32326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32246 eq32326
  have eq36166 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq36158
  have eq36200 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5846 x
       have i₂ := eq36166
       grind)
    | exact superpose eq36166 eq5846
    | exact resolve eq5846 eq36166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5846
  have eq36205 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq36166
       grind)
    | exact superpose eq36166 eq56
    | exact resolve eq56 eq36166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq36166
  have eq36207 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq210 eq36205
    | exact resolve eq36205 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq36205
  have eq36212 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36200
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36200
    | exact resolve eq36200 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36200
  have eq36224 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36207
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36207
    | exact resolve eq36207 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36207
  have eq36226 : (M.op x (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33194 eq36212
    | exact resolve eq36212 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36212
  have eq36236 : (M.op x (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36226
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36226
    | exact resolve eq36226 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq36226
  have eq36240 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33610 eq36236
    | exact resolve eq36236 eq33610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36236
  have eq36392 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36224 eq6371
    | exact resolve eq6371 eq36224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6371
  have eq36435 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq36392
    | exact resolve eq36392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36392
  have eq36781 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36240 eq36224
    | exact resolve eq36224 eq36240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36224 eq36240
  have eq36788 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq36781
  have eq36803 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36788 eq28
    | exact resolve eq28 eq36788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36788
  have eq36804 : y = (M.op x y) := by
    first
    | (have r₁ := eq36803
       have r₂ := eq36435
       grind)
    | exact resolve eq36803 eq36435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36435 eq36803
  have eq36806 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36804 eq21
    | exact resolve eq21 eq36804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq36855 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq36804 eq391
    | exact resolve eq391 eq36804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq36978 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq36855 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36855
    | (have j0 := eq36855 X0
       grind)
    | exact resolve eq36855 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq36855
  have eq37027 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36806
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36806
    | exact resolve eq36806 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36806
  have eq37086 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq36804 eq36978
    | exact resolve eq36978 eq36804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36804 eq36978
  have eq37135 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq33194 eq37027
    | exact resolve eq37027 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33194 eq37027
  have eq37878 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33610 eq37086
    | exact resolve eq37086 eq33610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33610 eq37086
  have eq38020 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37878 eq28
    | exact resolve eq28 eq37878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37878
  have eq38031 : False := by grind
  exact eq38031

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_pxy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq236 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq214 eq215
    | exact resolve eq215 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq517 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq516
    | exact resolve eq516 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq517 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq517
    | exact resolve eq517 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq519 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq518
    | exact resolve eq518 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq556 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq561 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq556
    | exact resolve eq556 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq556
  have eq722 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq726 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq731 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq726 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq726 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq3482 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq731
    | (have j0 := eq731 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq731 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq3498 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3482
    | (have j0 := eq3482 X0
       grind)
    | exact resolve eq3482 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3482
  have eq3499 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3498
  have eq3538 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3499 eq259
    | exact resolve eq259 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3543 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3499 eq35
    | exact resolve eq35 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3499
  have eq3569 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq506 eq3543
    | exact resolve eq3543 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq3613 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3569
       grind)
    | exact superpose eq3569 eq16
    | exact resolve eq16 eq3569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3913 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3538
    | exact resolve eq3538 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3918 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3538 eq561
    | exact resolve eq561 eq3538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq3538
  have eq4972 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq519 eq3918
    | exact resolve eq3918 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq5004 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4972
       have i₂ := eq3913 (M.op x sF0)
       grind)
    | exact superpose eq3913 eq4972
    | exact resolve eq4972 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq4972
  have eq5028 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq519 eq5004
    | exact resolve eq5004 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5254 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5028 eq15
    | exact resolve eq15 eq5028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq16624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16623
    | exact resolve eq16623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623
  have eq16635 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16624
       have r₂ := eq27
       grind)
    | exact resolve eq16624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16624
  have eq16639 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16635
    | exact resolve eq16635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16635
  have eq16643 : (τ (σ x)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16639 eq3613
    | exact resolve eq3613 eq16639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613 eq16639
  have eq16663 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq16643
    | exact resolve eq16643 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq16664 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16663
  have eq16670 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3569
       have i₂ := eq16664
       grind)
    | exact superpose eq16664 eq3569
    | exact resolve eq3569 eq16664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569 eq16664
  have eq16690 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16670
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16670
    | exact resolve eq16670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16670
  have eq16706 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16690 eq411
    | exact resolve eq411 eq16690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq16888 : (σ x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16706 eq16690
    | exact resolve eq16690 eq16706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16690 eq16706
  have eq16907 : (σ x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16888
  have eq16929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16907 eq235
    | exact resolve eq235 eq16907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16947 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16907 eq5028
    | exact resolve eq5028 eq16907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq16964 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq16947
    | exact resolve eq16947 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16947
  have eq16967 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16929
    | exact resolve eq16929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16929
  have eq16973 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16964 eq236
    | exact resolve eq236 eq16964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16976 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16973
    | exact resolve eq16973 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16973
  have eq17144 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16967 eq236
    | exact resolve eq236 eq16967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq17146 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq17148 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17144
    | exact resolve eq17144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17144
  have eq18053 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16976 eq489
    | exact resolve eq489 eq16976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18070 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16976 eq5028
    | exact resolve eq5028 eq16976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16976
  have eq18096 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16964 eq18070
    | exact resolve eq18070 eq16964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18070
  have eq18129 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18096
  have eq18132 : y = (σ y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18129
    | exact resolve eq18129 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18129
  have eq18558 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17148 eq489
    | exact resolve eq489 eq17148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17148
  have eq18824 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16964 eq18053
    | exact resolve eq18053 eq16964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964 eq18053
  have eq18858 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18824 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18824
  have eq18964 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16967 eq18558
    | exact resolve eq18558 eq16967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16967 eq18558
  have eq19000 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18964 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18964
  have eq19017 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19000 X0
       grind)
    | (have r₁ := eq19000 X0
       have r₂ := eq17146
       grind)
    | exact resolve eq19000 eq17146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17146 eq19000
  have eq19111 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18132 eq18858
    | exact resolve eq18858 eq18132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18132 eq18858
  have eq19162 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19111
  have eq19287 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq235 eq19017
    | exact resolve eq19017 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq19017
  have eq19786 : y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19162 x
       grind)
    | exact superpose eq19162 eq18
    | (have j1 := eq19162 x
       grind)
    | exact resolve eq18 eq19162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19162
  have eq19801 : y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq19786
  have eq19830 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq19801 eq20
    | exact resolve eq20 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19885 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq19801 eq489
    | exact resolve eq489 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19906 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq19801 eq5254
    | exact resolve eq5254 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19801
  have eq19908 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq19906
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19906
    | exact resolve eq19906 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19906
  have eq19928 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq19885 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19885
    | (have j0 := eq19885 X0
       grind)
    | exact resolve eq19885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19885
  have eq19982 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq19830
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19830
    | exact resolve eq19830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830
  have eq19983 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq19908
    | exact resolve eq19908 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19908
  have eq20024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq19982 eq26
    | exact resolve eq26 eq19982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19982
  have eq20704 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq19983 eq20024
    | exact resolve eq20024 eq19983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20714 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by grind
  clear eq20704
  have eq20965 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq20714 eq19928
    | exact resolve eq19928 eq20714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19928 eq20714
  have eq20973 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq20965
  have eq20986 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20973 eq27
    | exact resolve eq27 eq20973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20973
  have eq21015 : x = (σ x) := by
    first
    | (have r₁ := eq20986
       have r₂ := eq19983
       grind)
    | exact resolve eq20986 eq19983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19983 eq20986
  have eq21016 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21015 eq26
    | exact resolve eq26 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27396 : (σ y) = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21015 eq19287
    | exact resolve eq19287 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19287
  have eq27463 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27396 eq489
    | exact resolve eq489 eq27396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq27481 : (σ y) = (τ (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27396 eq5028
    | exact resolve eq5028 eq27396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27396
  have eq27513 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq27481
    | exact resolve eq27481 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27481
  have eq27524 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27513 eq26
    | exact resolve eq26 eq27513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27653 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21015 eq27524
    | exact resolve eq27524 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27524
  have eq27656 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27653
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27653
    | exact resolve eq27653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27653
  have eq27685 : x ≠ (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq32478 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq27463
    | (have j0 := eq27463 (σ x)
       grind)
    | exact resolve eq27463 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27463
  have eq32975 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27656 eq32478
    | exact resolve eq32478 eq27656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27656 eq32478
  have eq33023 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq32975
  have eq33029 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33023
       have r₂ := eq27685
       grind)
    | exact resolve eq33023 eq27685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27685 eq33023
  have eq33568 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33029 eq27513
    | exact resolve eq27513 eq33029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27513 eq33029
  have eq33573 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq33568
  have eq33719 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33573 eq5028
    | exact resolve eq5028 eq33573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5028
  have eq33721 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33573 eq5254
    | exact resolve eq5254 eq33573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254
  have eq33739 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33721
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33721
    | exact resolve eq33721 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33721
  have eq33740 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33719
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33719
    | exact resolve eq33719 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33719
  have eq33819 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33739
    | exact resolve eq33739 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33739
  have eq34203 : y = (τ y) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33573 eq33740
    | exact resolve eq33740 eq33573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33573 eq33740
  have eq34259 : y = (τ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq34203
  have eq34707 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq34259
       grind)
    | exact superpose eq34259 eq15
    | exact resolve eq15 eq34259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34259
  have eq34777 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34707
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34707
    | exact resolve eq34707 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq34707
  have eq34861 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34777 eq21016
    | exact resolve eq21016 eq34777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34777
  have eq34882 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34861
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34861
    | exact resolve eq34861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34861
  have eq35478 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34882 eq27
    | exact resolve eq27 eq34882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34882
  have eq35506 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35478
       have r₂ := eq33819
       grind)
    | exact resolve eq35478 eq33819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33819 eq35478
  have eq35516 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq35506 eq27
    | exact resolve eq27 eq35506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35518 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq35506 eq229
    | exact resolve eq229 eq35506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq35546 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq21016 eq35518
    | exact resolve eq35518 eq21016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21016 eq35518
  have eq35549 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq35506 eq35546
    | exact resolve eq35546 eq35506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35506 eq35546
  have eq35566 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq35549 eq519
    | exact resolve eq519 eq35549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq35549
  have eq35723 : x = (M.op x y) := by
    first
    | (have i₁ := eq35566 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35566
    | (have j0 := eq35566 y
       grind)
    | exact resolve eq35566 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35566
  have eq35867 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35723 eq20
    | exact resolve eq20 eq35723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35723
  have eq36057 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35867
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35867
    | exact resolve eq35867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35867
  have eq36122 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq21015 eq36057
    | exact resolve eq36057 eq21015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21015 eq36057
  have eq36164 : False := by grind
  exact eq36164

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_x_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
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
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq236 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq214 eq215
    | exact resolve eq215 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq517 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq516
    | exact resolve eq516 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq517 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq517
    | exact resolve eq517 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq519 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq518
    | exact resolve eq518 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq553 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq558 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq553
    | exact resolve eq553 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq553
  have eq755 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq759 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq764 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq759 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq759 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq3716 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq764
    | (have j0 := eq764 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq764 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq3732 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3716
    | (have j0 := eq3716 X0
       grind)
    | exact resolve eq3716 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3733 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3772 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3733 eq259
    | exact resolve eq259 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3777 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3733 eq35
    | exact resolve eq35 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3733
  have eq3803 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq506 eq3777
    | exact resolve eq3777 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3904 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq172 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq172
    | (have j0 := eq172 x
       grind)
    | exact resolve eq172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq3918 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3904
  have eq3928 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3918
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3918
    | exact resolve eq3918 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3918
  have eq3946 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3928
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq3928 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq3954 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3946 eq49
    | exact resolve eq49 eq3946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3946
  have eq3982 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3803
       grind)
    | exact superpose eq3803 eq16
    | exact resolve eq16 eq3803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4475 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3954 eq3982
    | exact resolve eq3982 eq3954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq4541 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3772
    | exact resolve eq3772 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq4546 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3772 eq558
    | exact resolve eq558 eq3772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq3772
  have eq5514 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq519 eq4546
    | exact resolve eq4546 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4546
  have eq5545 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq5514
       have i₂ := eq4541 (M.op x sF0)
       grind)
    | exact superpose eq4541 eq5514
    | exact resolve eq5514 eq4541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541 eq5514
  have eq5581 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq519 eq5545
    | exact resolve eq5545 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq5614 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5581 eq15
    | exact resolve eq15 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq16593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16592
    | exact resolve eq16592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592
  have eq16604 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq16593
       have r₂ := eq27
       grind)
    | exact resolve eq16593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16593
  have eq16608 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq16604
    | exact resolve eq16604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16604
  have eq16614 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16608 eq3954
    | exact resolve eq3954 eq16608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3954 eq16608
  have eq16634 : (τ (σ x)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16614
       have i₂ := eq4475
       grind)
    | exact superpose eq4475 eq16614
    | exact resolve eq16614 eq4475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475 eq16614
  have eq16642 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq16634
    | exact resolve eq16634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16634
  have eq16643 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16642
  have eq16647 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3803
       have i₂ := eq16643
       grind)
    | exact superpose eq16643 eq3803
    | exact resolve eq3803 eq16643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803 eq16643
  have eq16667 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16647
    | exact resolve eq16647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16647
  have eq16685 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16667 eq411
    | exact resolve eq411 eq16667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq17365 : (σ x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16685 eq16667
    | exact resolve eq16667 eq16685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16667 eq16685
  have eq17379 : (σ x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17365
  have eq17401 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17379 eq235
    | exact resolve eq235 eq17379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17417 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17379 eq5581
    | exact resolve eq5581 eq17379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17379
  have eq17434 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq17417
    | exact resolve eq17417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17417
  have eq17437 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17401
    | exact resolve eq17401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17401
  have eq17441 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17434 eq236
    | exact resolve eq236 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17445 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17441
    | exact resolve eq17441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17441
  have eq17624 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17437 eq236
    | exact resolve eq236 eq17437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq17625 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq17627 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17624
    | exact resolve eq17624 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17624
  have eq17876 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17445 eq489
    | exact resolve eq489 eq17445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17891 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17445 eq5581
    | exact resolve eq5581 eq17445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17445
  have eq17916 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17434 eq17891
    | exact resolve eq17891 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17891
  have eq17949 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq17916
  have eq17952 : y = (σ y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17949
    | exact resolve eq17949 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17949
  have eq18211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17627 eq489
    | exact resolve eq489 eq17627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627
  have eq18473 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17434 eq17876
    | exact resolve eq17876 eq17434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17434 eq17876
  have eq18507 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18473
  have eq18611 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17437 eq18211
    | exact resolve eq18211 eq17437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17437 eq18211
  have eq18647 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18611 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18611
  have eq18664 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18647 X0
       grind)
    | (have r₁ := eq18647 X0
       have r₂ := eq17625
       grind)
    | exact resolve eq18647 eq17625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17625 eq18647
  have eq18766 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17952 eq18507
    | exact resolve eq18507 eq17952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952 eq18507
  have eq18819 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18766
  have eq18967 : (σ y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq235 eq18664
    | exact resolve eq18664 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq18664
  have eq19478 : y = (M.op x y) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18819 x
       grind)
    | exact superpose eq18819 eq18
    | (have j1 := eq18819 x
       grind)
    | exact resolve eq18 eq18819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq19493 : y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq19478
  have eq19523 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq19493 eq20
    | exact resolve eq20 eq19493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19578 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq19493 eq489
    | exact resolve eq489 eq19493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19597 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq19493 eq5614
    | exact resolve eq5614 eq19493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19493
  have eq19599 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq19597
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19597
    | exact resolve eq19597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq19617 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq19578 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19578
    | (have j0 := eq19578 X0
       grind)
    | exact resolve eq19578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19578
  have eq19671 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq19523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19523
    | exact resolve eq19523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19523
  have eq19672 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq19599
    | exact resolve eq19599 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19599
  have eq19712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq19671 eq26
    | exact resolve eq26 eq19671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19671
  have eq20434 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq19672 eq19712
    | exact resolve eq19712 eq19672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19712
  have eq20444 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by grind
  clear eq20434
  have eq21169 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq20444 eq19617
    | exact resolve eq19617 eq20444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19617 eq20444
  have eq21177 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq21169
  have eq21188 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq21177 eq27
    | exact resolve eq27 eq21177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21177
  have eq21216 : x = (σ x) := by
    first
    | (have r₁ := eq21188
       have r₂ := eq19672
       grind)
    | exact resolve eq21188 eq19672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19672 eq21188
  have eq21217 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21216 eq26
    | exact resolve eq26 eq21216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27167 : (σ y) = (M.op x (M.op x y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21216 eq18967
    | exact resolve eq18967 eq21216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18967
  have eq28320 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27167 eq489
    | exact resolve eq489 eq27167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq28336 : (σ y) = (τ (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27167 eq5581
    | exact resolve eq5581 eq27167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27167
  have eq28368 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq28336
    | exact resolve eq28336 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28336
  have eq28379 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28368 eq26
    | exact resolve eq26 eq28368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28517 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21216 eq28379
    | exact resolve eq28379 eq21216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28379
  have eq28522 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28517
    | exact resolve eq28517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28517
  have eq28917 : x ≠ (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq33271 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq28320
    | (have j0 := eq28320 (σ x)
       grind)
    | exact resolve eq28320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28320
  have eq33822 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28522 eq33271
    | exact resolve eq33271 eq28522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28522 eq33271
  have eq33869 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq33822
  have eq33875 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33869
       have r₂ := eq28917
       grind)
    | exact resolve eq33869 eq28917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28917 eq33869
  have eq34468 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33875 eq28368
    | exact resolve eq28368 eq33875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28368 eq33875
  have eq34473 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq34468
  have eq34627 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34473 eq5581
    | exact resolve eq5581 eq34473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq34628 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34473 eq5614
    | exact resolve eq5614 eq34473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614
  have eq34644 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34628
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34628
    | exact resolve eq34628 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34628
  have eq34645 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34627
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34627
    | exact resolve eq34627 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34627
  have eq34725 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34644
    | exact resolve eq34644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34644
  have eq35140 : y = (τ y) ∨ x = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34473 eq34645
    | exact resolve eq34645 eq34473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34473 eq34645
  have eq35200 : y = (τ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq35140
  have eq35237 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq35200
       grind)
    | exact superpose eq35200 eq15
    | exact resolve eq15 eq35200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35200
  have eq35312 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35237
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35237
    | exact resolve eq35237 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35237
  have eq35402 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35312 eq21217
    | exact resolve eq21217 eq35312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35312
  have eq35423 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35402
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35402
    | exact resolve eq35402 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35402
  have eq35587 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35423 eq27
    | exact resolve eq27 eq35423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35423
  have eq35614 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35587
       have r₂ := eq34725
       grind)
    | exact resolve eq35587 eq34725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34725 eq35587
  have eq35632 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq35614 eq27
    | exact resolve eq27 eq35614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35634 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq35614 eq229
    | exact resolve eq229 eq35614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq35661 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq21217 eq35634
    | exact resolve eq35634 eq21217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21217 eq35634
  have eq35664 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq35614 eq35661
    | exact resolve eq35661 eq35614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35614 eq35661
  have eq35687 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq35664 eq519
    | exact resolve eq519 eq35664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq35664
  have eq35849 : x = (M.op x y) := by
    first
    | (have i₁ := eq35687 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35687
    | (have j0 := eq35687 y
       grind)
    | exact resolve eq35687 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35687
  have eq35990 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35849 eq20
    | exact resolve eq20 eq35849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35849
  have eq36178 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35990
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35990
    | exact resolve eq35990 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35990
  have eq36244 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq21216 eq36178
    | exact resolve eq36178 eq21216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21216 eq36178
  have eq36285 : False := by grind
  exact eq36285

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq515 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq515
    | exact resolve eq515 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq517 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq516 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq516
    | exact resolve eq516 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq517
    | exact resolve eq517 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq556 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq557 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq411
    | exact resolve eq411 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq556
    | exact resolve eq556 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq674 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq678 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq678 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq678 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq3354 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq682
    | (have j0 := eq682 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq682 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq3369 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3354
    | (have j0 := eq3354 X0
       grind)
    | exact resolve eq3354 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq3354
  have eq3370 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3405 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3370 eq259
    | exact resolve eq259 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3410 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3370 eq35
    | exact resolve eq35 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3370
  have eq3435 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq506 eq3410
    | exact resolve eq3410 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3480 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3435
       grind)
    | exact superpose eq3435 eq16
    | exact resolve eq16 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3617 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3405
    | exact resolve eq3405 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3622 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3405 eq561
    | exact resolve eq561 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq3623 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3405 eq557
    | exact resolve eq557 eq3405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq3405
  have eq4803 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq518 eq3622
    | exact resolve eq3622 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq4834 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4803
       have i₂ := eq3617 (M.op x sF0)
       grind)
    | exact superpose eq3617 eq4803
    | exact resolve eq4803 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4854 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq518 eq4834
    | exact resolve eq4834 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834
  have eq15918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq15919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq15918
    | exact resolve eq15918 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15918
  have eq15931 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15919
       have r₂ := eq27
       grind)
    | exact resolve eq15919 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15919
  have eq15936 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq15931
    | exact resolve eq15931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15931
  have eq15938 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15936 eq3480
    | exact resolve eq3480 eq15936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480 eq15936
  have eq15959 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq15938
    | exact resolve eq15938 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15938
  have eq15960 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15959
  have eq15964 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3435
       have i₂ := eq15960
       grind)
    | exact superpose eq15960 eq3435
    | exact resolve eq3435 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435 eq15960
  have eq15984 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15964
    | exact resolve eq15964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15964
  have eq15998 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15984 eq411
    | exact resolve eq411 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16177 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15998 eq15984
    | exact resolve eq15984 eq15998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984 eq15998
  have eq16194 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16177
  have eq16211 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16194 eq235
    | exact resolve eq235 eq16194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq16194
  have eq16246 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16211
    | exact resolve eq16211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16211
  have eq16247 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16246
  have eq16252 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16247 eq229
    | exact resolve eq229 eq16247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq16255 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16252
    | exact resolve eq16252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16252
  have eq16427 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16255 eq518
    | exact resolve eq518 eq16255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq16438 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16255 eq4854
    | exact resolve eq4854 eq16255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854 eq16255
  have eq16461 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16247 eq16438
    | exact resolve eq16438 eq16247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438
  have eq16494 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq16461
  have eq16496 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16494
    | exact resolve eq16494 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16494
  have eq17320 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16247 eq16427
    | exact resolve eq16427 eq16247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16247 eq16427
  have eq17348 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17320
  have eq17799 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16496 eq17348
    | exact resolve eq17348 eq16496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16496 eq17348
  have eq17837 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17799
  have eq18035 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17837 y
       grind)
    | exact superpose eq17837 eq18
    | (have j1 := eq17837 y
       grind)
    | exact resolve eq18 eq17837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17837
  have eq18088 : x = (M.op x y) := by grind
  clear eq18035
  have eq18118 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18088 eq20
    | exact resolve eq20 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18164 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18088 eq214
    | exact resolve eq214 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq18202 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18164
    | exact resolve eq18164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18164
  have eq18247 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18118
    | exact resolve eq18118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18248 : x = (M.op x x) := by
    first
    | exact superpose eq18088 eq18202
    | exact resolve eq18202 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202
  have eq18286 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18247 eq26
    | exact resolve eq26 eq18247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18436 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq18248
       grind)
    | exact resolve eq13 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18438 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq3623 x
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq3623
    | exact resolve eq3623 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq18446 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq18436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18436
  have eq18453 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq18438
       have i₂ := eq3617 x
       grind)
    | exact superpose eq3617 eq18438
    | exact resolve eq18438 eq3617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617 eq18438
  have eq18462 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq18453
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq18453
    | exact resolve eq18453 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18453
  have eq18471 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq18088 eq18462
    | exact resolve eq18462 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18477 : x = (τ x) := by
    first
    | (have i₁ := eq18471
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq18471
    | exact resolve eq18471 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18471
  have eq18481 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq18477
       grind)
    | exact superpose eq18477 eq15
    | exact resolve eq15 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq18535 : x = (σ x) := by
    first
    | (have i₁ := eq18481
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18481
    | exact resolve eq18481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18481
  have eq18548 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq18247 eq18535
    | exact resolve eq18535 eq18247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18247 eq18535
  have eq18817 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq18548 eq18286
    | exact resolve eq18286 eq18548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18286
  have eq18940 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq18446 X0
       grind)
    | exact superpose eq18446 eq411
    | exact resolve eq411 eq18446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq19018 : ∀ X0 : G, (M.op x x) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | exact superpose eq18088 eq18940
    | exact resolve eq18940 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18940
  have eq19075 : ∀ X0 : G, x = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq19018 X0
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq19018
    | exact resolve eq19018 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018
  have eq19293 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq411 (k X0 x) X0
       have i₂ := eq19075 X0
       grind)
    | exact superpose eq19075 eq411
    | exact resolve eq411 eq19075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq19075
  have eq19301 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq18088 eq19293
    | exact resolve eq19293 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18088 eq19293
  have eq19315 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq19301 X0
       have i₂ := eq18248
       grind)
    | exact superpose eq18248 eq19301
    | exact resolve eq19301 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18248 eq19301
  have eq19353 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18817 eq19315
    | exact resolve eq19315 eq18817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18817 eq19315
  have eq19458 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq19353 eq27
    | exact resolve eq27 eq19353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19353
  have eq19473 : False := by grind
  exact eq19473

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq51 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq209 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq222 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq209 eq221
    | exact resolve eq221 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq250 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq385 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq403 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq222 eq385
    | exact resolve eq385 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq385
  have eq476 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq51 x x X2 X4 X5
       have i₂ := eq403 x x
       grind)
    | exact superpose eq403 eq51
    | exact resolve eq51 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq477 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq476 X2 x x
       have i₂ := eq403 x x
       grind)
    | exact superpose eq403 eq476
    | exact resolve eq476 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq489 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq477 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq477 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq502 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq503 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq209 eq502
    | exact resolve eq502 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq504 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq503 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq503
    | exact resolve eq503 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq503
  have eq505 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq209 eq504
    | exact resolve eq504 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq504
  have eq541 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X0 X1 X2
       have i₂ := eq493 X0
       grind)
    | exact superpose eq493 eq14
    | exact resolve eq14 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq541 X0 x x
       have i₂ := eq403 x x
       grind)
    | exact superpose eq403 eq541
    | exact resolve eq541 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq600 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq605 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq605 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq605 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq605 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq3371 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq493 eq609
    | (have j0 := eq609 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq609 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq3386 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq477 eq3371
    | (have j0 := eq3371 X0
       grind)
    | exact resolve eq3371 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3387 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3386 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3416 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3387 eq250
    | exact resolve eq250 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq3422 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3387 eq37
    | exact resolve eq37 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3387
  have eq3445 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq493 eq3422
    | exact resolve eq3422 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3470 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3445
       grind)
    | exact superpose eq3445 eq16
    | exact resolve eq16 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3773 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq3781 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3773
  have eq3788 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3781
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq3781
    | exact resolve eq3781 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq3781
  have eq3812 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3788
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq3788 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq3828 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3812 eq86
    | exact resolve eq86 eq3812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3812
  have eq3862 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq3828 eq3470
    | exact resolve eq3470 eq3828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq4151 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq493 eq3416
    | exact resolve eq3416 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq4156 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3416 eq546
    | exact resolve eq546 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq3416
  have eq4241 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4151 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4151
    | exact resolve eq4151 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq4241 X0
       grind)
    | exact superpose eq4241 eq15
    | exact resolve eq15 eq4241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4705 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq403 (σ X0) (σ X0)
       have i₂ := eq4385 X0
       grind)
    | exact superpose eq4385 eq403
    | exact resolve eq403 eq4385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385
  have eq5067 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq505 eq4156
    | exact resolve eq4156 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq5094 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq5067
       have i₂ := eq4151 (M.op x sF0)
       grind)
    | exact superpose eq4151 eq5067
    | exact resolve eq5067 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151 eq5067
  have eq5117 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq505 eq5094
    | exact resolve eq5094 eq505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq5094
  have eq5138 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5117 eq15
    | exact resolve eq15 eq5117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117
  have eq30356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq30357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq30356
    | exact resolve eq30356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30356
  have eq30368 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq30357
       have r₂ := eq28
       grind)
    | exact resolve eq30357 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30357
  have eq30372 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30368 eq3828
    | exact resolve eq3828 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30368
  have eq30413 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30372
       have i₂ := eq3862
       grind)
    | exact superpose eq3862 eq30372
    | exact resolve eq30372 eq3862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30372
  have eq30421 : y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq30413
    | exact resolve eq30413 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30413
  have eq30422 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq30421
  have eq30430 : (τ (σ x)) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30422 eq3828
    | exact resolve eq3828 eq30422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828 eq30422
  have eq30473 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30430
       have i₂ := eq3862
       grind)
    | exact superpose eq3862 eq30430
    | exact resolve eq30430 eq3862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862 eq30430
  have eq30484 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq30473
    | exact resolve eq30473 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30473
  have eq30485 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq30484
  have eq30504 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq403 y y
       have i₂ := eq30485
       grind)
    | exact superpose eq30485 eq403
    | exact resolve eq403 eq30485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30509 : x ≠ y ∨ x = (M.op y y) := by grind
  have eq30930 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30504
       have i₂ := eq30485
       grind)
    | exact superpose eq30485 eq30504
    | exact resolve eq30504 eq30485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30485 eq30504
  have eq30978 : y = (M.op x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30930
       have r₂ := eq30509
       grind)
    | exact resolve eq30930 eq30509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30509 eq30930
  have eq31324 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30978 eq477
    | exact resolve eq477 eq30978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31339 : y = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30978 eq5138
    | exact resolve eq5138 eq30978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30978
  have eq31381 : x = (M.op y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31339
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31339
    | exact resolve eq31339 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31339
  have eq31403 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq4705 y
       have i₂ := eq31381
       grind)
    | exact superpose eq31381 eq4705
    | exact resolve eq4705 eq31381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31409 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq403 y y
       have i₂ := eq31381
       grind)
    | exact superpose eq31381 eq403
    | exact resolve eq403 eq31381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31381
  have eq31418 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31409
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31409
    | exact resolve eq31409 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31409
  have eq31420 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31403
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31403
    | exact resolve eq31403 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31403
  have eq31434 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31420
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31420
    | exact resolve eq31420 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31420
  have eq31438 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq27 eq31434
    | exact resolve eq31434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31434
  have eq31457 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31418 eq5138
    | exact resolve eq5138 eq31418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31498 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq21 eq31457
    | exact resolve eq31457 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31457
  have eq32098 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31438 eq31418
    | exact resolve eq31418 eq31438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31418 eq31438
  have eq32104 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq32098
  have eq32461 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32104 eq28
    | exact resolve eq28 eq32104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32104
  have eq32462 : y = (σ y) := by
    first
    | (have r₁ := eq32461
       have r₂ := eq31498
       grind)
    | exact resolve eq32461 eq31498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31498 eq32461
  have eq32463 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq32462 eq27
    | exact resolve eq27 eq32462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34705 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31324 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31324
    | (have j0 := eq31324 x
       grind)
    | exact resolve eq31324 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31324
  have eq34824 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4705 y
       have i₂ := eq34705
       grind)
    | exact superpose eq34705 eq4705
    | exact resolve eq4705 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705
  have eq34830 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq403 y y
       have i₂ := eq34705
       grind)
    | exact superpose eq34705 eq403
    | exact resolve eq403 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq34705
  have eq34839 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34830
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34830
    | exact resolve eq34830 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34830
  have eq34844 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34824
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34824
    | exact resolve eq34824 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34824
  have eq34862 : (M.op x (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32462 eq34844
    | exact resolve eq34844 eq32462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34844
  have eq34874 : (M.op x (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34862
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34862
    | exact resolve eq34862 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq34862
  have eq34879 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32463 eq34874
    | exact resolve eq34874 eq32463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34874
  have eq35847 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34839 eq5138
    | exact resolve eq5138 eq34839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5138
  have eq35895 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq35847
    | exact resolve eq35847 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35847
  have eq36266 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34879 eq34839
    | exact resolve eq34839 eq34879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34839 eq34879
  have eq36272 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq36266
  have eq36284 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36272 eq28
    | exact resolve eq28 eq36272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36272
  have eq36290 : y = (M.op x y) := by
    first
    | (have r₁ := eq36284
       have r₂ := eq35895
       grind)
    | exact resolve eq36284 eq35895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35895 eq36284
  have eq36403 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36290 eq21
    | exact resolve eq21 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq36456 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq36290 eq477
    | exact resolve eq477 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq36594 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq36456 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36456
    | (have j0 := eq36456 X0
       grind)
    | exact resolve eq36456 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq36456
  have eq36647 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36403
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36403
    | exact resolve eq36403 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36403
  have eq36713 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq36290 eq36594
    | exact resolve eq36594 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36290 eq36594
  have eq36766 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq32462 eq36647
    | exact resolve eq36647 eq32462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32462 eq36647
  have eq37271 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32463 eq36713
    | exact resolve eq36713 eq32463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32463 eq36713
  have eq37414 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37271 eq28
    | exact resolve eq28 eq37271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37271
  have eq37426 : False := by grind
  exact eq37426

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation4438 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 X0) ∨ (k (M.op X2 X0) X0) = (M.op (M.op X2 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X0) X0
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X2 X0) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X2) X0) X0
       have r₂ := eq16 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) x) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq28 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op X1 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq41
    | exact resolve eq41 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq853
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq853
    | exact resolve eq853 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq856 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq854
    | exact resolve eq854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq856 eq839
    | exact resolve eq839 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq866
       have r₂ := eq27
       grind)
    | exact resolve eq866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq878 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq873 eq196
    | exact resolve eq196 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq873 eq181
    | exact resolve eq181 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq873 eq12
    | (have j0 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq873
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq873
       grind)
    | exact resolve eq12 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq873 eq13
    | exact resolve eq13 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq873 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq893 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq881
       have r₂ := eq883
       grind)
    | exact resolve eq881 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq883
  have eq894 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq879
    | exact resolve eq879 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq897 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq893 eq98
    | exact resolve eq98 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq893
  have eq903 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq897
    | exact resolve eq897 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq942 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq878 eq894
    | exact resolve eq894 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq952 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq942
  have eq964 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq952 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq964
    | exact resolve eq964 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq856 eq976
    | exact resolve eq976 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq981 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq980
       have r₂ := eq27
       grind)
    | exact resolve eq980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1474 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq880 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1475 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq856 eq1474
    | exact resolve eq1474 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1474
  have eq1480 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1475 eq952
    | exact resolve eq952 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq1475
  have eq1493 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1480
  have eq1507 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1493
       have r₂ := eq981
       grind)
    | exact resolve eq1493 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1517 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq189
    | exact resolve eq189 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1518 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq180
    | exact resolve eq180 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : x ≠ y ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq13
    | exact resolve eq13 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1522 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq28
    | exact resolve eq28 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1523 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq176 x x X0
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq176
    | exact resolve eq176 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1534 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1523 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1523
    | (have j0 := eq1523 X0
       grind)
    | exact resolve eq1523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1536 : y = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1520
       have r₂ := eq1522
       grind)
    | exact resolve eq1520 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520 eq1522
  have eq1537 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1518
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1518
    | exact resolve eq1518 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1541 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1534 x
       have i₂ := eq189 x
       grind)
    | (have i₁ := eq1534 y
       have i₂ := eq189 x
       grind)
    | exact superpose eq189 eq1534
    | (have j0 := eq1534 y
       grind)
    | exact resolve eq1534 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1542 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1537 eq1541
    | exact resolve eq1541 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1544 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1536
       grind)
    | exact superpose eq1536 eq40
    | exact resolve eq40 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1546 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1544
    | exact resolve eq1544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1548 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1546
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1546
    | exact resolve eq1546 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1571 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1542 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1542
       grind)
    | exact resolve eq13 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1573 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1542 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1580 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1571
  have eq1582 : (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1537 eq1580
    | exact resolve eq1580 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1593 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1582 eq40
    | exact resolve eq40 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq1594 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1593
    | exact resolve eq1593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1796 : x = (k x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq849 x
       have i₂ := eq1507
       grind)
    | exact superpose eq1507 eq849
    | exact resolve eq849 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2023 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1796
       grind)
    | exact superpose eq1796 eq41
    | exact resolve eq41 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2024 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2023
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2023
    | exact resolve eq2023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq2185 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1573 eq36
    | exact resolve eq36 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2190 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq2185
    | exact resolve eq2185 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2206 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2024 eq839
    | exact resolve eq839 eq2024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2221 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2190 eq809
    | (have j0 := eq809 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq809 eq2190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2222 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq181 eq2221
    | exact resolve eq2221 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2226 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1507 eq2222
    | exact resolve eq2222 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2343 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2206 eq181
    | exact resolve eq181 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2366 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq2343
    | exact resolve eq2343 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq2376 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1517 eq2366
    | exact resolve eq2366 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517 eq2366
  have eq2385 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1537 eq2376
    | exact resolve eq2376 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq2660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2190 eq807
    | (have j0 := eq807 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq807 (σ x) (σ (M.op x y))
       have r₂ := eq2190
       grind)
    | exact resolve eq807 eq2190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2681 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2660
  have eq2693 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1507 eq2681
    | exact resolve eq2681 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq2681
  have eq2706 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1594 eq2693
    | exact resolve eq2693 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq2693
  have eq3397 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2226 eq2385
    | exact resolve eq2385 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq3415 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3397
  have eq3434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2706 eq3415
    | exact resolve eq3415 eq2706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq3444 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3434
       have r₂ := eq27
       grind)
    | exact resolve eq3434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3434
  have eq3465 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3444 eq28
    | exact resolve eq28 eq3444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3474 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3465
  have eq3486 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1548 eq3474
    | exact resolve eq3474 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3542 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3486 eq2226
    | exact resolve eq2226 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226 eq3486
  have eq3553 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3542
  have eq3560 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2706 eq3553
    | exact resolve eq3553 eq2706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706 eq3553
  have eq3561 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3560
  have eq3581 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3561 eq28
    | exact resolve eq28 eq3561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561
  have eq3590 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3581
  have eq3604 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1548 eq3590
    | exact resolve eq3590 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq3590
  have eq3605 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3604
  have eq4196 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3605 eq29
    | exact resolve eq29 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq4228 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq4196
    | exact resolve eq4196 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4196
  have eq4229 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4228
  have eq4236 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4229 eq29
    | exact resolve eq29 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4229
  have eq4256 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4236
    | exact resolve eq4236 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4236
  have eq4257 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4256
  have eq4260 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4257
       grind)
    | exact superpose eq4257 eq18
    | exact resolve eq18 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4261 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4257
       grind)
    | exact superpose eq4257 eq24
    | exact resolve eq24 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4264 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq4257
       grind)
    | exact superpose eq4257 eq185
    | (have r₁ := eq185
       have r₂ := eq4257
       grind)
    | exact resolve eq185 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4269 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq830
       have i₂ := eq4257
       grind)
    | exact superpose eq4257 eq830
    | exact resolve eq830 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq4285 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1796
       have i₂ := eq4257
       grind)
    | exact superpose eq4257 eq1796
    | exact resolve eq1796 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq4290 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq4264
  have eq4291 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1537 eq4285
    | exact resolve eq4285 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq4285
  have eq4292 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4291
  have eq4296 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4261
    | exact resolve eq4261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4261
  have eq4383 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4292 eq1573
    | exact resolve eq1573 eq4292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq4292
  have eq4390 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4383
  have eq4396 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4296 eq4390
    | exact resolve eq4390 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390
  have eq5537 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (k (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq6026 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4269 eq36
    | exact resolve eq36 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269
  have eq6040 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6026
    | exact resolve eq6026 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6026
  have eq6044 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4296 eq6040
    | exact resolve eq6040 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq6046 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4396 eq6044
    | exact resolve eq6044 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq6044
  have eq6069 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6046 eq807
    | (have j0 := eq807 (σ x) (σ x)
       grind)
    | (have r₁ := eq807 (σ x) (σ x)
       have r₂ := eq6046
       grind)
    | exact resolve eq807 eq6046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6046
  have eq6071 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6069
  have eq6072 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6071
  have eq6095 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6072 eq181
    | exact resolve eq181 eq6072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6132 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6072 eq6095
    | exact resolve eq6095 eq6072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072 eq6095
  have eq6197 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6132 eq894
    | exact resolve eq894 eq6132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq6132
  have eq6239 : y = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6197
       have r₂ := eq981
       grind)
    | exact resolve eq6197 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq6197
  have eq6252 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4257 eq6239
    | exact resolve eq6239 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257 eq6239
  have eq6253 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6252
  have eq6262 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq6253
       grind)
    | exact superpose eq6253 eq180
    | exact resolve eq180 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6263 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq849 x
       have i₂ := eq6253
       grind)
    | exact superpose eq6253 eq849
    | exact resolve eq849 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq6267 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq6253
       grind)
    | exact superpose eq6253 eq28
    | exact resolve eq28 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6282 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq6267
  have eq6293 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4260 eq6262
    | exact resolve eq6262 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260 eq6262
  have eq6318 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6282
       grind)
    | exact superpose eq6282 eq40
    | exact resolve eq40 eq6282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282
  have eq6328 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6318
    | exact resolve eq6318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6330 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6328
    | exact resolve eq6328 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6328
  have eq6332 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4296 eq6330
    | exact resolve eq6330 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6330
  have eq6339 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6293 eq4290
    | exact resolve eq4290 eq6293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6358 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq6339
  have eq6384 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6332 eq809
    | (have j0 := eq809 (σ x) (σ x) x
       grind)
    | exact resolve eq809 eq6332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6387 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181 eq6384
    | exact resolve eq6384 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6598 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6263 eq42
    | exact resolve eq42 eq6263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq6263
  have eq6607 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6598
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6598
    | exact resolve eq6598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6598
  have eq6609 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4296 eq6607
    | exact resolve eq6607 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6611 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6293 eq6609
    | exact resolve eq6609 eq6293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293 eq6609
  have eq6612 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6611
  have eq6617 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6612 eq839
    | exact resolve eq839 eq6612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq6612
  have eq6666 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6617 eq181
    | exact resolve eq181 eq6617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6673 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6617 eq176
    | exact resolve eq176 eq6617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq6701 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq6673
    | (have j0 := eq6673 X0
       grind)
    | exact resolve eq6673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq6704 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6666
    | exact resolve eq6666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6710 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq6701
    | (have j0 := eq6701 (σ y)
       grind)
    | exact resolve eq6701 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq6701
  have eq6714 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6704 eq6710
    | exact resolve eq6710 eq6704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6710
  have eq6771 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6714 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq6714
       grind)
    | exact resolve eq13 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6773 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6714 eq28
    | (have j0 := eq28 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq6788 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6771
  have eq6791 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6617 eq6773
    | exact resolve eq6773 eq6617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6617 eq6773
  have eq6792 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6704 eq6788
    | exact resolve eq6788 eq6704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6704 eq6788
  have eq7286 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6792 eq142
    | exact resolve eq142 eq6792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6792
  have eq8038 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6791 eq91
    | exact resolve eq91 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6791
  have eq10676 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (k (τ (M.op (σ x) (σ y))) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8038 eq807
    | (have j0 := eq807 x (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq807 x (τ (M.op (σ x) (σ y)))
       have r₂ := eq8038
       grind)
    | exact resolve eq807 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10677 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8038 eq809
    | (have j0 := eq809 x (τ (M.op (σ x) (σ y))) x
       grind)
    | exact resolve eq809 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq8038
  have eq10678 : (k (τ (M.op (σ x) (σ y))) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10676
  have eq10683 : (M.op (M.op x y) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10677 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq10677
    | exact resolve eq10677 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10677
  have eq10684 : (k (τ (M.op (σ x) (σ y))) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6253 eq10678
    | exact resolve eq10678 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10678
  have eq10687 : (k (M.op x y) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4290 eq10683
    | exact resolve eq10683 eq4290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290 eq10683
  have eq10688 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7286 eq10684
    | exact resolve eq10684 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286 eq10684
  have eq10690 : (k (M.op x y) x) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6253 eq10687
    | exact resolve eq10687 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6253 eq10687
  have eq10691 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10688 eq10690
    | exact resolve eq10690 eq10688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688 eq10690
  have eq10692 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6358 eq10691
    | exact resolve eq10691 eq6358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358 eq10691
  have eq10693 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10692
  have eq10699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10693 eq14
    | exact resolve eq14 eq10693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10693
  have eq10714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10699
    | exact resolve eq10699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699
  have eq10718 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10714
       have r₂ := eq27
       grind)
    | exact resolve eq10714 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10714
  have eq10720 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10718 eq27
    | exact resolve eq27 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718
  have eq10814 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10720
       have r₂ := eq4296
       grind)
    | exact resolve eq10720 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10720
  have eq10843 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10814 eq27
    | exact resolve eq27 eq10814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10877 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10814 eq6387
    | exact resolve eq6387 eq10814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq10881 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10877
  have eq10890 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10881
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq10881 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10881
  have eq10910 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6332 eq10890
    | exact resolve eq10890 eq6332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10890
  have eq10923 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4296 eq10843
    | exact resolve eq10843 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296 eq10843
  have eq10929 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq10923
  have eq11121 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10910 eq181
    | exact resolve eq181 eq10910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq10910
  have eq11163 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11121
    | exact resolve eq11121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11121
  have eq11180 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10814 eq11163
    | exact resolve eq11163 eq10814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10814 eq11163
  have eq11181 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11180
  have eq11214 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11181 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq11181
       grind)
    | exact resolve eq13 eq11181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11232 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11214
  have eq11271 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11232 eq6332
    | exact resolve eq6332 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6332 eq11232
  have eq11282 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq11271
  have eq11290 : x = (M.op x y) := by
    first
    | (have r₁ := eq11282
       have r₂ := eq10929
       grind)
    | exact resolve eq11282 eq10929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10929 eq11282
  have eq11307 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq18
    | exact resolve eq18 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11308 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq22
    | exact resolve eq22 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq11309 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq36
    | exact resolve eq36 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq11310 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq40
    | exact resolve eq40 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq11311 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq180
    | exact resolve eq180 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11312 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq189 x
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq189
    | exact resolve eq189 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq11315 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq903
       have i₂ := eq11290
       grind)
    | exact superpose eq11290 eq903
    | exact resolve eq903 eq11290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq11290
  have eq11458 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11308 eq20
    | exact resolve eq20 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11564 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k X0 (M.op x y))) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11307 eq808
    | (have j0 := eq808 (M.op x y) (M.op (M.op x y) (k X0 (M.op x y))) x
       grind)
    | exact resolve eq808 eq11307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq11879 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) X1) (M.op x y)) (M.op x y)) := by
    intro X1
    first
    | exact superpose eq11311 eq178
    | exact resolve eq178 eq11311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq11912 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op (M.op x y) X1) (M.op x y)) (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq11879 X1
       have i₂ := eq5537 sF0 X1
       grind)
    | exact superpose eq5537 eq11879
    | exact resolve eq11879 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537 eq11879
  have eq11921 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq11312 eq11912
    | exact resolve eq11912 eq11312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312 eq11912
  have eq12274 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq11921 eq11310
    | exact resolve eq11310 eq11921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11310
  have eq13838 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11315 eq11564
    | (have j0 := eq11564 (M.op x y)
       grind)
    | exact resolve eq11564 eq11315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11564
  have eq13874 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11307 eq13838
    | exact resolve eq13838 eq11307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13838
  have eq13875 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13874
  have eq13897 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13875 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq13875
       grind)
    | exact resolve eq13 eq13875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13915 : y ≠ (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13875
  have eq13916 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13897
  have eq13927 : y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13916 eq11315
    | exact resolve eq11315 eq13916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11315 eq13916
  have eq13942 : y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13927
  have eq13952 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq13942
       have r₂ := eq13915
       grind)
    | exact resolve eq13942 eq13915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13915 eq13942
  have eq13976 : y = (k y (M.op x y)) := by
    first
    | exact superpose eq13952 eq11921
    | exact resolve eq11921 eq13952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11921
  have eq13977 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq13952 eq12274
    | exact resolve eq12274 eq13952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12274
  have eq13982 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq13952 eq11311
    | exact resolve eq11311 eq13952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11311 eq13952
  have eq14024 : y = (M.op x y) := by
    first
    | exact superpose eq11307 eq13982
    | exact resolve eq13982 eq11307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307 eq13982
  have eq14025 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13977
    | exact resolve eq13977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13977
  have eq14040 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14024
       grind)
    | exact superpose eq14024 eq24
    | exact resolve eq24 eq14024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14041 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq14024
       grind)
    | exact superpose eq14024 eq37
    | exact resolve eq37 eq14024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14024
  have eq14094 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq11309 eq14041
    | exact resolve eq14041 eq11309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11309 eq14041
  have eq14095 : (σ x) = (σ y) := by
    first
    | exact superpose eq11308 eq14040
    | exact resolve eq14040 eq11308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11308 eq14040
  have eq14107 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14095 eq26
    | exact resolve eq26 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14265 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13976 eq37
    | exact resolve eq37 eq13976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13976
  have eq14277 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq14094 eq14265
    | exact resolve eq14265 eq14094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14094 eq14265
  have eq14282 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq14277
    | exact resolve eq14277 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14277
  have eq14284 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq11458 eq14282
    | exact resolve eq14282 eq11458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14282
  have eq14285 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14284
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14284
    | exact resolve eq14284 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14284
  have eq14286 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14095 eq14285
    | exact resolve eq14285 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14285
  have eq14683 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq14025 eq807
    | (have j0 := eq807 (σ y) (σ x)
       grind)
    | exact resolve eq807 eq14025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq14025
  have eq14686 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq14683
       have r₂ := eq14095
       grind)
    | exact resolve eq14683 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14683
  have eq14694 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq14095 eq14686
    | exact resolve eq14686 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14686
  have eq14701 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq14107 eq14694
    | exact resolve eq14694 eq14107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694
  have eq14706 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq14286 eq14701
    | exact resolve eq14701 eq14286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14286 eq14701
  have eq14710 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14095 eq14706
    | exact resolve eq14706 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14095 eq14706
  have eq14713 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14107 eq14710
    | exact resolve eq14710 eq14107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107 eq14710
  have eq14714 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14713
  have eq14718 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq14714 eq27
    | exact resolve eq27 eq14714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14714
  have eq14774 : False := by grind
  exact eq14774

/-- `Equation4439`: `x ◇ (y ◇ x) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pyx_Equation4439 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4439 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4439.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X0) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X0) X0 X3
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X3 (M.op X2 X0)
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) X3 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq180 X0 x X2 X3
       have i₂ := eq16 X0 X3 (M.op x X0)
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq186 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) X1
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X1 (M.op X0 x)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op x y) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq191 x X1
       have i₂ := eq16 sF0 X1 x
       grind)
    | exact superpose eq16 eq191
    | exact resolve eq191 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq195 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq194 X1
       have i₂ := eq181 X1
       grind)
    | exact superpose eq181 eq194
    | exact resolve eq194 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq196 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq182 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq182
    | exact resolve eq182 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq198 x X1
       have i₂ := eq16 sF4 X1 x
       grind)
    | exact superpose eq16 eq198
    | exact resolve eq198 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | exact superpose eq182 eq201
    | exact resolve eq201 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq212 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq195 sF0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq195
    | exact resolve eq195 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (M.op (k (σ x) (σ x)) X0) (σ x)) = (M.op (k (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq196 eq16
    | exact resolve eq16 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op (M.op (k (σ x) (σ x)) X0) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq186 sF2 (M.op sF4 sF2)
       grind)
    | exact superpose eq186 eq219
    | exact resolve eq219 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq222 : ∀ X0 : G, (M.op (M.op (k (σ x) (σ x)) X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq182 eq220
    | exact resolve eq220 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq224 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (σ x) (M.op X0 (σ x))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq222 x
       have i₂ := eq186 sF2 x
       grind)
    | exact superpose eq186 eq222
    | exact resolve eq222 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq225 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | (have i₁ := eq224 x
       have i₂ := eq16 sF2 sF2 (M.op x sF2)
       grind)
    | exact superpose eq16 eq224
    | exact resolve eq224 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq226 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq182 eq225
    | exact resolve eq225 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq227 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq202 sF4
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq202
    | exact resolve eq202 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq227 eq16
    | exact resolve eq16 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq174 (k sF4 sF4)
       grind)
    | exact superpose eq174 eq346
    | exact resolve eq346 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq348 : ∀ X0 : G, (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq347 x
       have i₂ := eq186 sF4 x
       grind)
    | exact superpose eq186 eq347
    | exact resolve eq347 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq349 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq348 x
       have i₂ := eq16 sF4 sF4 (M.op x sF4)
       grind)
    | exact superpose eq16 eq348
    | exact resolve eq348 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq350 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq202 eq349
    | exact resolve eq349 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq351 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq350
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq350
    | exact resolve eq350 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq385 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq469 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq385
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq636 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202 (M.op X0 X1)
       have i₂ := eq177 X0 X1 sF4 x
       grind)
    | (have i₁ := eq202 (M.op X0 x)
       have i₂ := eq177 X0 X1 sF4 x
       grind)
    | exact superpose eq177 eq202
    | exact resolve eq202 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq202 eq674
    | exact resolve eq674 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq715 : ∀ X0 X1 : G, (M.op (τ X0) (M.op X1 (τ X0))) = (M.op (τ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (τ X0) X1
       have i₂ := eq469 X0 X0
       grind)
    | exact superpose eq469 eq186
    | exact resolve eq186 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (k X0 X0)
       have i₂ := eq186 X0 (k X0 X0)
       grind)
    | exact superpose eq186 eq174
    | exact resolve eq174 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (k X0 X0)) X0)) = (M.op (M.op (k X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (k X0 X0) X1 X2
       have i₂ := eq186 X0 (M.op X1 (k X0 X0))
       grind)
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (k X0 X0)) X0)) = (M.op (M.op X0 (M.op X2 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq723 X0 X1 X2
       have i₂ := eq186 X0 X2
       grind)
    | exact superpose eq186 eq723
    | exact resolve eq723 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq733 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq718 X0
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq718
    | exact resolve eq718 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq736 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 (k X0 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq729 X0 X1 x
       have i₂ := eq16 X0 X1 (M.op x X0)
       grind)
    | exact superpose eq16 eq729
    | exact resolve eq729 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq739 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq733 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq733
    | exact resolve eq733 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq857 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op (τ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq636 (τ X0) X1 X2
       have i₂ := eq469 X0 X0
       grind)
    | exact superpose eq469 eq636
    | exact resolve eq636 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) (k X0 X0)) = (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (k X0 X0) X2
       have i₂ := eq636 X0 X1 (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq636 eq187
    | exact resolve eq187 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) (M.op x y))) = (M.op (M.op x y) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 (k X0 X0)
       have i₂ := eq636 X0 X1 sF0
       grind)
    | exact superpose eq636 eq195
    | exact resolve eq195 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (k X0 X0)
       have i₂ := eq636 X0 X1 sF4
       grind)
    | exact superpose eq636 eq202
    | exact resolve eq202 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq202 eq891
    | exact resolve eq891 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq894 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq195 eq889
    | exact resolve eq889 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq896 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) = (M.op (M.op X0 (M.op X2 X0)) (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq887 X0 X1 X2
       have i₂ := eq186 X0 X2
       grind)
    | exact superpose eq186 eq887
    | exact resolve eq887 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq934 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) X0)) = (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq896 X0 X1 x
       have i₂ := eq16 X0 (k X0 X0) (M.op x X0)
       grind)
    | exact superpose eq16 eq896
    | exact resolve eq896 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq951 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq186 X0 X0
       grind)
    | exact superpose eq186 eq934
    | exact resolve eq934 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq962 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (k X0 X0))) = (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq951
    | exact resolve eq951 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq967 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op X0 X1) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq962
    | exact resolve eq962 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq962
  have eq1009 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq675 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq675
    | (have j0 := eq675 x X0 y
       grind)
    | exact resolve eq675 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq675
    | (have j0 := eq675 (σ x) (σ y) X0
       grind)
    | exact resolve eq675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq675 eq202
    | exact resolve eq202 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1036 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq675 eq226
    | exact resolve eq226 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq675
  have eq1044 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq892 eq1036
    | exact resolve eq1036 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1050 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq892 eq1015
    | (have j1 := eq892 (σ x) (σ y)
       grind)
    | exact resolve eq1015 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1053 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (k x x)) := by
    first
    | exact superpose eq892 eq1009
    | (have j1 := eq892 x y
       grind)
    | exact resolve eq1009 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1080 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq227 eq1044
    | exact resolve eq1044 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq1044
  have eq1086 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq1050
    | exact resolve eq1050 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1116 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1080 eq182
    | exact resolve eq182 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1116
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq1116
    | exact resolve eq1116 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1134 : x ≠ (M.op x y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1035 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1035
    | exact resolve eq1035 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1341 : ∀ X0 : G, (M.op (M.op (k x x) X0) (M.op (σ x) (σ y))) = (M.op (k x x) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1053 eq16
    | exact resolve eq16 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1350 : ∀ X0 : G, (M.op (M.op (k x x) X0) (M.op (σ x) (σ y))) = (M.op x (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq186 x (M.op sF4 sF0)
       grind)
    | exact superpose eq186 eq1341
    | exact resolve eq1341 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1352 : ∀ X0 : G, (M.op (M.op (k x x) X0) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1350 X0
       have i₂ := eq181 (M.op sF4 sF0)
       grind)
    | exact superpose eq181 eq1350
    | exact resolve eq1350 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1353 : ∀ X0 : G, (M.op (M.op (k x x) X0) (M.op (σ x) (σ y))) = (M.op (M.op x y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq894 eq1352
    | exact resolve eq1352 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1354 : ∀ X0 : G, (M.op (M.op x y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op x (M.op X0 x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1353 X0
       have i₂ := eq186 x X0
       grind)
    | exact superpose eq186 eq1353
    | exact resolve eq1353 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1355 : (M.op x (M.op (M.op (σ x) (σ y)) x)) = (M.op (M.op x y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1354 x
       have i₂ := eq16 x sF4 (M.op x x)
       grind)
    | exact superpose eq16 eq1354
    | exact resolve eq1354 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1356 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1355
       have i₂ := eq181 sF4
       grind)
    | exact superpose eq181 eq1355
    | exact resolve eq1355 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1398 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1124 eq187
    | exact resolve eq187 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1408 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1398
       have i₂ := eq186 sF4 sF2
       grind)
    | exact superpose eq186 eq1398
    | exact resolve eq1398 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1416 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq892 eq1408
    | exact resolve eq1408 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq1408
  have eq1422 : (M.op (σ x) (k (σ x) (σ x))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1086 eq1416
    | exact resolve eq1416 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq1416
  have eq1575 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq39
    | exact resolve eq39 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1576 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1575
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1575
    | exact resolve eq1575 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq1578 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq1576
    | exact resolve eq1576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1578 eq1168
    | exact resolve eq1168 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1586
       have r₂ := eq27
       grind)
    | exact resolve eq1586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1608 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1593 eq1140
    | (have r₁ := eq1140
       have r₂ := eq1593
       grind)
    | exact resolve eq1140 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1609 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1593 eq1261
    | exact resolve eq1261 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1608
  have eq1614 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1613
  have eq1624 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1614 eq1578
    | exact resolve eq1578 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1628 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1614 eq141
    | exact resolve eq141 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq1630 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1624
  have eq1633 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1628
    | exact resolve eq1628 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1636 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1633
       have r₂ := eq1134
       grind)
    | exact resolve eq1633 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1633
  have eq1642 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1636
       grind)
    | exact superpose eq1636 eq39
    | exact resolve eq39 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1645 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1642
    | exact resolve eq1642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1651 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1645 eq1168
    | exact resolve eq1168 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq1645
  have eq1655 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1651
  have eq1664 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1630 eq31
    | exact resolve eq31 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq1664
    | exact resolve eq1664 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq1686 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1685
  have eq1689 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1686 eq28
    | exact resolve eq28 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1691 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1686 eq85
    | exact resolve eq85 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1686
  have eq1708 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq72 eq1691
    | exact resolve eq1691 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1691
  have eq1710 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1689
    | exact resolve eq1689 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1714 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1710
       grind)
    | exact superpose eq1710 eq18
    | exact resolve eq18 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1734 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1714 eq195
    | exact resolve eq195 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1753 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1734
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq1734
    | exact resolve eq1734 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1916 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op (M.op X1 X4) (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X1 (M.op (M.op X0 X2) X3) X4
       have i₂ := eq179 X0 X2 X3 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1655 eq1080
    | exact resolve eq1080 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2084 : (k (σ y) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1655 eq1124
    | exact resolve eq1124 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq2086 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (k X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1655 eq1261
    | exact resolve eq1261 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq2089 : (M.op (M.op x y) (σ y)) = (M.op (M.op x y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1655 eq1356
    | exact resolve eq1356 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq2236 : (M.op (M.op x y) (M.op x y)) = (M.op x (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1753 eq181
    | exact resolve eq181 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq2252 : (k (M.op x y) (M.op x y)) = (M.op x (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2236
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq2236
    | exact resolve eq2236 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2534 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2081 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2545 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2534
  have eq2673 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1609 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1609
    | exact resolve eq1609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq2995 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 x))) = (M.op (M.op X0 X1) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq2252 eq176
    | exact resolve eq176 eq2252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3119 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X2) x
       have i₂ := eq176 X1 X0 X2 x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3258 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op X0 X1) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2995 X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq2995
    | exact resolve eq2995 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq3719 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op (M.op x y) X0) (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq184 x (M.op X0 x) x
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2252 eq184
    | exact resolve eq184 eq2252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq3774 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op (M.op X0 x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq184 X0 x x
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq184
    | exact resolve eq184 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3797 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0 (M.op X0 x) x
       have i₂ := eq184 X0 x X1
       grind)
    | exact superpose eq184 eq176
    | exact resolve eq176 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3843 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3774 x
       have i₂ := eq176 sF0 x x x
       grind)
    | exact superpose eq176 eq3774
    | exact resolve eq3774 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq3868 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) (M.op (M.op X0 (k (M.op x y) (M.op x y))) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3723 X0
       have i₂ := eq186 sF0 (M.op X0 (k sF0 sF0))
       grind)
    | exact superpose eq186 eq3723
    | exact resolve eq3723 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq3872 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op x y) (M.op (M.op X1 (M.op (M.op x y) X0)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3719 x X1
       have i₂ := eq16 sF0 (M.op X1 (M.op sF0 x)) x
       grind)
    | exact superpose eq16 eq3719
    | exact resolve eq3719 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3891 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3843 X0
       have i₂ := eq3797 X0 sF0
       grind)
    | exact superpose eq3797 eq3843
    | exact resolve eq3843 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq3898 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) (M.op X0 (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq195 eq3868
    | exact resolve eq3868 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3902 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq195 eq3872
    | exact resolve eq3872 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3872
  have eq3914 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3898 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq3898
    | exact resolve eq3898 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898
  have eq3918 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3902 X0 X1
       have i₂ := eq181 X1
       grind)
    | exact superpose eq181 eq3902
    | exact resolve eq3902 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq3946 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (k (M.op x y) (M.op x y))) X2)) = (M.op (M.op x y) (M.op (M.op X0 (k (M.op x y) (M.op x y))) (M.op (M.op x y) X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq3914 eq176
    | exact resolve eq176 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3966 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (k (M.op x y) (M.op x y)))) = (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (k (M.op x y) (M.op x y))) X2)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq3918 eq3946
    | exact resolve eq3946 eq3918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918 eq3946
  have eq3972 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op X0 (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (M.op (M.op (M.op X0 (k (M.op x y) (M.op x y))) X2) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq3966 X0 X2 X2
       have i₂ := eq16 sF0 (M.op (M.op X0 (k sF0 sF0)) X2) X2
       grind)
    | exact superpose eq16 eq3966
    | exact resolve eq3966 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966
  have eq3973 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op X0 (k (M.op x y) (M.op x y)))) = (M.op (M.op x y) (M.op (M.op X0 (k (M.op x y) (M.op x y))) X2)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X2
    first
    | exact superpose eq195 eq3972
    | exact resolve eq3972 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq3974 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op X0 (k (M.op x y) (M.op x y))) X2)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X2
    first
    | exact superpose eq3914 eq3973
    | exact resolve eq3973 eq3914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914 eq3973
  have eq3984 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = (M.op (M.op X0 X1) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq2084 eq176
    | exact resolve eq176 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4014 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op X0 X1) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3984 X0 X1
       have i₂ := eq3797 X0 sF2
       grind)
    | exact superpose eq3797 eq3984
    | exact resolve eq3984 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4071 : ∀ X0 : G, (M.op (σ y) (τ X0)) = (M.op (σ y) (τ (k X0 X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2086 (τ X0)
       have i₂ := eq469 X0 X0
       grind)
    | exact superpose eq469 eq2086
    | exact resolve eq2086 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4392 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (k (M.op x y) (M.op x y))) = (M.op (M.op (M.op X0 X2) X3) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3258 eq179
    | exact resolve eq179 eq3258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3258
  have eq4641 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op X0 X1) X2)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3974 X0 X2
       have i₂ := eq177 X0 (k sF0 sF0) X2 x
       grind)
    | (have i₁ := eq3974 X0 X2
       have i₂ := eq177 X0 X1 X2 (k sF0 sF0)
       grind)
    | exact superpose eq177 eq3974
    | exact resolve eq3974 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op X1 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq3974 X0 (M.op x (M.op X0 (k sF0 sF0)))
       have i₂ := eq184 X0 (k sF0 sF0) x
       grind)
    | exact superpose eq184 eq3974
    | exact resolve eq3974 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq3974
  have eq4704 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (k X0 X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq894 eq4644
    | exact resolve eq4644 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644
  have eq4730 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (M.op (M.op x y) (τ (k X0 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4704 (τ X0)
       have i₂ := eq469 X0 X0
       grind)
    | exact superpose eq469 eq4704
    | exact resolve eq4704 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704
  have eq4876 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (k (M.op X0 X1) (M.op X0 X1))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4641 X0 X1 (M.op X0 X1)
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq4641
    | exact resolve eq4641 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4641
  have eq6088 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (k (k X0 X0) (k X0 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4876 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq4876
    | exact resolve eq4876 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876
  have eq6622 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X1) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X1 X3) (k X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq175 X1 X1 (k X0 X0) X3
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq175
    | exact resolve eq175 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq7006 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X1) = (M.op X0 (M.op (M.op (M.op X1 X3) (k X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6622 X0 X1 X2 X3
       have i₂ := eq16 X0 (M.op (M.op X1 X3) (k X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq16 eq6622
    | exact resolve eq6622 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6622
  have eq7137 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X3) X0)) = (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7006 X0 X1 X2 X3
       have i₂ := eq736 X0 (M.op X1 X3)
       grind)
    | exact superpose eq736 eq7006
    | exact resolve eq7006 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq7006
  have eq7233 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 X3) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7137 X0 X1 x X3
       have i₂ := eq179 X0 (M.op X1 X0) x X1
       grind)
    | exact superpose eq179 eq7137
    | exact resolve eq7137 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq7137
  have eq8290 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (M.op (M.op x y) (k (τ (k X0 X0)) (τ (k X0 X0)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6088 (τ X0)
       have i₂ := eq469 X0 X0
       grind)
    | exact superpose eq469 eq6088
    | exact resolve eq6088 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6088
  have eq8362 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (M.op (M.op x y) (τ (k (k X0 X0) (k X0 X0)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8290 X0
       have i₂ := eq469 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq469 eq8290
    | exact resolve eq8290 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8290
  have eq9307 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k y (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2673 y
       have i₂ := eq1708 y
       grind)
    | exact superpose eq1708 eq2673
    | exact resolve eq2673 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq9379 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k y (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq9307
  have eq9395 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq41 eq9379
    | exact resolve eq9379 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9379
  have eq9401 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9395
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9395
    | exact resolve eq9395 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9395
  have eq9406 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq9401
    | exact resolve eq9401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9401
  have eq9411 : (σ x) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1593 eq9406
    | exact resolve eq9406 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9406
  have eq9416 : (σ x) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1630 eq9411
    | exact resolve eq9411 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9411
  have eq10714 : (k (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2545 eq2084
    | exact resolve eq2084 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq10754 : (k (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq10714
  have eq13180 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X4) X5) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op x y)) X5) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3 X4 X5
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f13180_14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
      intro X0 X1 X2 X3
      grind
    have f13180_23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
      intro X0 X1 X2
      grind
    have f13180_24 : (M.op (M.op (M.op X0 X3) X4) X5) ≠ (M.op (M.op (M.op (M.op X0 X1) X2) (M.op x y)) X5) := by grind
    have f13180_44 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X4) X5) = (M.op (M.op (M.op X0 X1) X2) X5) := by
      intro X0 X1 X2 X3 X4 X5
      first
      | (have i₁ := f13180_14 (M.op X0 X3) X4 X5 X2
         have i₂ := f13180_14 X0 X3 X2 X1
         grind)
      | (have i₁ := f13180_14 (M.op X0 X3) X4 X5 X2
         have i₂ := f13180_14 X0 X1 X2 X3
         grind)
      | exact superpose f13180_14 f13180_14
      | exact resolve f13180_14 f13180_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13180_119 : (M.op (M.op (M.op X0 X3) X4) X5) ≠ (M.op (M.op (M.op X0 (M.op X2 X0)) (M.op x y)) X5) := by
      first
      | (have i₁ := f13180_24
         have i₂ := f13180_23 X0 X2 X1
         grind)
      | exact superpose f13180_23 f13180_24
      | exact resolve f13180_24 f13180_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13180_132 : False := by
      first
      | (have r₁ := f13180_119
         have r₂ := f13180_44 X0 (M.op X2 X0) (M.op x y) X3 X4 X5
         grind)
      | (have r₁ := f13180_119
         have r₂ := f13180_44 X0 X3 X4 (M.op X2 X0) (M.op x y) X5
         grind)
      | exact resolve f13180_119 f13180_44
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f13180_132
  clear eq4392
  have eq29450 : (M.op (M.op x y) (k (σ y) (σ y))) = (M.op x (M.op (σ x) x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4014 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4014
    | (have j0 := eq4014 x y
       grind)
    | exact resolve eq4014 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29677 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (k (σ y) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4014 eq16
    | exact resolve eq16 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq30045 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29677 x
       have i₂ := eq186 sF3 x
       grind)
    | exact superpose eq186 eq29677
    | exact resolve eq29677 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29677
  have eq30099 : (M.op (M.op x y) (σ x)) = (M.op (M.op x y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29450
       have i₂ := eq181 sF2
       grind)
    | exact superpose eq181 eq29450
    | exact resolve eq29450 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29450
  have eq30157 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30045 X0
       have i₂ := eq3797 X0 sF3
       grind)
    | exact superpose eq3797 eq30045
    | exact resolve eq30045 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30045
  have eq30465 : (M.op (M.op x y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30099 eq2089
    | exact resolve eq2089 eq30099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30099
  have eq30567 : (M.op (M.op x y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30465
  have eq30904 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op X0 X1) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq30157 eq16
    | exact resolve eq16 eq30157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69233 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10754 eq30904
    | exact resolve eq30904 eq10754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754 eq30904
  have eq69266 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq69233
  have eq69344 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq182 eq69266
    | exact resolve eq69266 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq69266
  have eq69406 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1080 eq69344
    | exact resolve eq69344 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69344
  have eq69462 : (k (σ y) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1655 eq69406
    | exact resolve eq69406 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69406
  have eq69513 : (k (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2545 eq69462
    | exact resolve eq69462 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69462
  have eq83399 : (M.op y (M.op x y)) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq3891 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3891
    | (have j0 := eq3891 y
       grind)
    | exact resolve eq3891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83626 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq195 x
       have i₂ := eq3891 sF0
       grind)
    | exact superpose eq3891 eq195
    | exact resolve eq195 eq3891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq83682 : (M.op (M.op x y) x) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq894 eq83626
    | exact resolve eq83626 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83626
  have eq83766 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq212 eq83682
    | exact resolve eq83682 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83682
  have eq96965 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op (M.op (M.op (M.op X0 X1) X2) (M.op x y)) X3)) = (M.op (M.op X3 X6) (M.op (M.op X0 X4) X5)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16 X3 (M.op (M.op X0 X4) X5) X6
       have i₂ := eq13180 X0 X1 X2 X4 X5 X3
       grind)
    | exact superpose eq13180 eq16
    | exact resolve eq16 eq13180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180
  have eq98636 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X6) (M.op (M.op X0 X4) X5)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq96965 X0 X1 X2 X0 X4 X5 X6
       have i₂ := eq7233 X0 (M.op (M.op X0 X1) X2) sF0
       grind)
    | exact superpose eq7233 eq96965
    | exact resolve eq96965 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96965
  have eq98922 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op X3 (M.op (M.op X0 X1) X3)) = (M.op (M.op X3 X6) (M.op (M.op X0 X4) X5)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq98636 X0 X1 x X3 X4 X5 X6
       have i₂ := eq7233 X3 (M.op X0 X1) x
       grind)
    | exact superpose eq7233 eq98636
    | exact resolve eq98636 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98636
  have eq99096 : ∀ X0 X3 X4 X5 X6 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op X3 X6) (M.op (M.op X0 X4) X5)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X3 X4 X5 X6
    first
    | (have i₁ := eq98922 X0 x X3 X4 X5 X6
       have i₂ := eq7233 X3 X0 x
       grind)
    | exact superpose eq7233 eq98922
    | exact resolve eq98922 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98922
  have eq99271 : ∀ X0 X1 X2 X3 : G, (M.op X0 (k X0 X0)) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X3)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99096 X0 X0 X2 X3 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq99096
    | exact resolve eq99096 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99096
  have eq110797 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 X0) X1) (M.op (M.op (k X0 X0) X2) X3)) = (M.op (M.op X0 X4) (k (k X0 X0) (k X0 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq636 X0 X4 (k (k X0 X0) (k X0 X0))
       have i₂ := eq99271 (k X0 X0) X1 X2 X3
       grind)
    | exact superpose eq99271 eq636
    | exact resolve eq636 eq99271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq111864 : ∀ X0 X1 X2 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op (k X0 X0) X1) (M.op (M.op (k X0 X0) X2) X3)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110797 X0 X1 X2 X3 x
       have i₂ := eq967 X0 x
       grind)
    | exact superpose eq967 eq110797
    | exact resolve eq110797 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq110797
  have eq112156 : ∀ X0 X1 X2 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op (k X0 X0) X1) (M.op (M.op X0 (M.op X2 X0)) X3)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111864 X0 X1 X2 X3
       have i₂ := eq186 X0 X2
       grind)
    | exact superpose eq186 eq111864
    | exact resolve eq111864 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111864
  have eq112375 : ∀ X0 X1 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op (k X0 X0) X1) (M.op X0 (M.op X3 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X3
    first
    | (have i₁ := eq112156 X0 X1 x X3
       have i₂ := eq16 X0 X3 (M.op x X0)
       grind)
    | exact superpose eq16 eq112156
    | exact resolve eq112156 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112156
  have eq112510 : ∀ X0 X1 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X3 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X3
    first
    | (have i₁ := eq112375 X0 X1 X3
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq112375
    | exact resolve eq112375 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112375
  have eq112598 : ∀ X0 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (M.op (M.op X0 (M.op X3 X0)) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X3
    first
    | (have i₁ := eq112510 X0 x X3
       have i₂ := eq16 X0 (M.op X0 (M.op X3 X0)) (M.op x X0)
       grind)
    | exact superpose eq16 eq112510
    | exact resolve eq112510 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112510
  have eq112653 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112598 X0 x
       have i₂ := eq3119 X0 X0 (M.op x X0)
       grind)
    | exact superpose eq3119 eq112598
    | exact resolve eq112598 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112598
  have eq112682 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112653 X0
       have i₂ := eq3797 X0 X0
       grind)
    | exact superpose eq3797 eq112653
    | exact resolve eq112653 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112653
  have eq112705 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq112682 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq112682
    | exact resolve eq112682 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112682
  have eq112763 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (M.op (M.op x y) (τ (M.op X0 (k X0 X0)))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8362 X0
       have i₂ := eq112705 X0
       grind)
    | exact superpose eq112705 eq8362
    | exact resolve eq8362 eq112705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8362 eq112705
  have eq112824 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (M.op (M.op x y) (τ (M.op X0 (k X0 X0)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq112763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112763
  have eq112944 : (M.op (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1422 eq112824
    | exact resolve eq112824 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112824
  have eq113230 : (M.op (M.op x y) x) = (M.op (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq112944
    | exact resolve eq112944 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112944
  have eq113260 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq83766 eq113230
    | exact resolve eq113230 eq83766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113230
  have eq113561 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq113260 eq4730
    | exact resolve eq4730 eq113260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4730 eq113260
  have eq113782 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq113561
  have eq113948 : ∀ X0 : G, (M.op (M.op (τ (M.op (σ x) (σ y))) X0) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq113782 eq16
    | exact resolve eq16 eq113782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113782
  have eq114197 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq113948 x
       have i₂ := eq857 sF4 x sF0
       grind)
    | exact superpose eq857 eq113948
    | exact resolve eq113948 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq113948
  have eq123827 : ∀ X0 X1 : G, (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) (M.op (M.op (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y))) X1)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq114197 eq99271
    | exact resolve eq99271 eq114197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99271 eq114197
  have eq123848 : ∀ X0 X1 : G, (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) (M.op (M.op (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y))) X1)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq123827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123827
  have eq123928 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (τ (M.op (σ x) (σ y))) (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq123848 x x
       have i₂ := eq1916 (τ sF4) (τ (k sF4 sF4)) (k sF0 sF0) x x
       grind)
    | exact superpose eq1916 eq123848
    | exact resolve eq123848 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916 eq123848
  have eq123995 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (τ (M.op (σ x) (σ y))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq123928
       have i₂ := eq3797 (τ (k sF4 sF4)) (τ sF4)
       grind)
    | exact superpose eq3797 eq123928
    | exact resolve eq123928 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123928
  have eq124052 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq123995
       have i₂ := eq715 (k sF4 sF4) (τ sF4)
       grind)
    | exact superpose eq715 eq123995
    | exact resolve eq123995 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123995
  have eq124087 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq351 eq124052
    | exact resolve eq124052 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124052
  have eq124111 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124087
       have i₂ := eq469 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq469 eq124087
    | exact resolve eq124087 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124087
  have eq124125 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq351 eq124111
    | exact resolve eq124111 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124111
  have eq124134 : (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124125
       have i₂ := eq174 (τ (k sF4 sF4))
       grind)
    | exact superpose eq174 eq124125
    | exact resolve eq124125 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124125
  have eq124139 : (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) = (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124134
       have i₂ := eq469 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq469 eq124134
    | exact resolve eq124134 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq124134
  have eq124143 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq351 eq124139
    | exact resolve eq124139 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq124139
  have eq124151 : (τ (k (σ x) (σ x))) = (M.op (τ (k (σ x) (σ x))) (τ (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1593 eq124143
    | exact resolve eq124143 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124143
  have eq124330 : (τ (k (σ x) (σ x))) = (M.op (τ (k (σ x) (σ x))) (τ (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq124151
  have eq124359 : (τ (k (σ x) (σ x))) = (M.op (τ (k (σ x) (σ x))) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq124330
    | exact resolve eq124330 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124330
  have eq124381 : (k x x) = (M.op (k x x) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq97 eq124359
    | exact resolve eq124359 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124359
  have eq124396 : (k x x) = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq124381
       have i₂ := eq186 x x
       grind)
    | exact superpose eq186 eq124381
    | exact resolve eq124381 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124381
  have eq124408 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq124396
       have i₂ := eq181 x
       grind)
    | exact superpose eq181 eq124396
    | exact resolve eq124396 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124396
  have eq124416 : (k x x) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq83766 eq124408
    | exact resolve eq124408 eq83766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83766 eq124408
  have eq124441 : (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2673 x
       have i₂ := eq124416
       grind)
    | exact superpose eq124416 eq2673
    | exact resolve eq2673 eq124416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq124486 : (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq124441
  have eq124505 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124486
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124486
    | exact resolve eq124486 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124486
  have eq124521 : (M.op (σ x) (σ x)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq41 eq124505
    | exact resolve eq124505 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124505
  have eq124530 : (M.op (σ x) (σ x)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq124521
    | exact resolve eq124521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124521
  have eq124538 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124530
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq124530
    | exact resolve eq124530 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124530
  have eq124542 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1630 eq124538
    | exact resolve eq124538 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq124538
  have eq124544 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9416 eq124542
    | exact resolve eq124542 eq9416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9416 eq124542
  have eq124559 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq124544 eq141
    | exact resolve eq141 eq124544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq124544
  have eq124585 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq124559
    | exact resolve eq124559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124559
  have eq124592 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124416
       have i₂ := eq124585
       grind)
    | exact superpose eq124585 eq124416
    | exact resolve eq124416 eq124585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124416
  have eq124598 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq186 x X0
       have i₂ := eq124585
       grind)
    | exact superpose eq124585 eq186
    | exact resolve eq186 eq124585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124585
  have eq124616 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq124592
  have eq124618 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq124598 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq124598
    | exact resolve eq124598 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124598
  have eq125704 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1714
       have i₂ := eq124618 sF0
       grind)
    | exact superpose eq124618 eq1714
    | exact resolve eq1714 eq124618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq124618
  have eq125994 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq125704
  have eq126121 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq125994
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq125994
    | exact resolve eq125994 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125994
  have eq126445 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq126121 eq124616
    | exact resolve eq124616 eq126121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124616 eq126121
  have eq126467 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq126445
  have eq126502 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq126467 eq31
    | exact resolve eq31 eq126467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126467
  have eq126540 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq126502
    | exact resolve eq126502 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126502
  have eq126541 : x = (M.op x y) ∨ x = y := by grind
  clear eq126540
  have eq126553 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq126541
       grind)
    | exact superpose eq126541 eq18
    | exact resolve eq18 eq126541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126554 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq126541
       grind)
    | exact superpose eq126541 eq22
    | exact resolve eq22 eq126541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126541
  have eq126572 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq126554
    | exact resolve eq126554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126554
  have eq697264 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 X0 X2
       have i₂ := eq177 X0 X2 X0 X1
       grind)
    | (have i₁ := eq188 X0 X2
       have i₂ := eq177 X0 X1 X0 X2
       grind)
    | exact superpose eq177 eq188
    | exact resolve eq188 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq698979 : ∀ X0 X1 : G, (M.op (σ y) (τ (M.op X0 X1))) = (M.op (σ y) (τ (M.op X0 (M.op (M.op X0 X1) X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4071 (M.op X0 X1)
       have i₂ := eq188 X0 X1
       grind)
    | exact superpose eq188 eq4071
    | exact resolve eq4071 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq699046 : ∀ X0 X1 : G, (M.op (σ y) (τ (M.op X0 X1))) = (M.op (σ y) (τ (M.op X0 (M.op X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq698979 X0 X1
       have i₂ := eq7233 X0 X0 X1
       grind)
    | exact superpose eq7233 eq698979
    | exact resolve eq698979 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698979
  have eq699690 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq697264 X0 x X2
       have i₂ := eq7233 X0 X0 x
       grind)
    | exact superpose eq7233 eq697264
    | exact resolve eq697264 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7233 eq697264
  have eq699704 : ∀ X0 X1 : G, (M.op (σ y) (τ (M.op X0 X1))) = (M.op (σ y) (τ (M.op X0 (k X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq699046 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq699046
    | exact resolve eq699046 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699046
  have eq700121 : ∀ X0 X2 : G, (M.op X0 (k X0 X0)) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq699690 X0 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq699690
    | exact resolve eq699690 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699690
  have eq705807 : ∀ X0 : G, (M.op (σ y) (τ (M.op (σ x) X0))) = (M.op (σ y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1422 eq699704
    | exact resolve eq699704 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699704
  have eq707911 : ∀ X0 : G, (M.op (σ y) (τ (k (σ y) (σ y)))) = (M.op (σ y) (τ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1655 eq705807
    | exact resolve eq705807 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705807
  have eq708012 : ∀ X0 : G, (M.op (σ y) (k y y)) = (M.op (σ y) (τ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq115 eq707911
    | exact resolve eq707911 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707911
  have eq708088 : ∀ X0 : G, (M.op (σ y) y) = (M.op (σ y) (τ (M.op (σ x) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2086 eq708012
    | exact resolve eq708012 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708012
  have eq708297 : (M.op (σ y) y) = (M.op (σ y) (τ (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq708088 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq708088
    | exact resolve eq708088 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708329 : ∀ X0 : G, (M.op (τ (M.op (σ x) X0)) (M.op (σ x) (τ (M.op (σ x) X0)))) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq708088 eq30157
    | exact resolve eq30157 eq708088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30157 eq708088
  have eq709147 : ∀ X0 : G, (M.op (τ (M.op (σ x) X0)) (M.op (σ x) (τ (M.op (σ x) X0)))) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq708329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708329
  have eq709228 : ∀ X0 : G, (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) = (M.op (τ (k (M.op (σ x) X0) (M.op (σ x) X0))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq709147 X0
       have i₂ := eq715 (M.op sF2 X0) sF2
       grind)
    | exact superpose eq715 eq709147
    | exact resolve eq709147 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq709147
  have eq709236 : (M.op (σ y) (k x x)) = (M.op (σ y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq97 eq708297
    | exact resolve eq708297 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708297
  have eq709248 : ∀ X0 : G, (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) = (M.op (τ (M.op (σ x) (k (σ x) (σ x)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq709228 x
       have i₂ := eq700121 sF2 x
       grind)
    | exact superpose eq700121 eq709228
    | exact resolve eq709228 eq700121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709228
  have eq709252 : (M.op (σ y) (k (M.op x y) (M.op x y))) = (M.op (σ y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1593 eq709236
    | exact resolve eq709236 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593 eq709236
  have eq709259 : ∀ X0 : G, (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ x))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq196 eq709248
    | exact resolve eq709248 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq709248
  have eq709262 : (M.op (σ y) (M.op x y)) = (M.op (σ y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2086 eq709252
    | exact resolve eq709252 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086 eq709252
  have eq709264 : ∀ X0 : G, (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1080 eq709259
    | exact resolve eq709259 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq709259
  have eq709267 : ∀ X0 : G, (M.op (τ (k (σ y) (σ y))) (σ x)) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1655 eq709264
    | exact resolve eq709264 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709264
  have eq709269 : ∀ X0 : G, (M.op (k y y) (σ x)) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq115 eq709267
    | exact resolve eq709267 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq709267
  have eq709270 : ∀ X0 : G, (M.op y (M.op (σ x) y)) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq709269 X0
       have i₂ := eq186 y sF2
       grind)
    | exact superpose eq186 eq709269
    | exact resolve eq709269 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709269
  have eq709271 : ∀ X0 : G, (M.op y (M.op (σ x) y)) = (M.op (τ (M.op (σ x) X0)) (M.op (σ y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq709262 eq709270
    | exact resolve eq709270 eq709262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709262 eq709270
  have eq742291 : (M.op y (M.op (σ x) y)) = (M.op (τ (k (σ x) (σ x))) (M.op (σ y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq709271 sF2
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq709271
    | exact resolve eq709271 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709271
  have eq743138 : (M.op y (M.op (σ x) y)) = (M.op (k x x) (M.op (σ y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq97 eq742291
    | exact resolve eq742291 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq742291
  have eq743269 : (M.op y (M.op (σ x) y)) = (M.op x (M.op (M.op (σ y) (M.op x y)) x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq743138
       have i₂ := eq186 x (M.op sF3 sF0)
       grind)
    | exact superpose eq186 eq743138
    | exact resolve eq743138 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq743138
  have eq743372 : (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op y (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq743269
       have i₂ := eq181 (M.op sF3 sF0)
       grind)
    | exact superpose eq181 eq743269
    | exact resolve eq743269 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq743269
  have eq743443 : (M.op (M.op x y) (k (σ y) (σ y))) = (M.op y (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq894 eq743372
    | exact resolve eq743372 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq743372
  have eq743497 : (M.op (M.op x y) (σ y)) = (M.op y (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2089 eq743443
    | exact resolve eq743443 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089 eq743443
  have eq743537 : (M.op (M.op x y) (σ x)) = (M.op y (M.op (σ x) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30567 eq743497
    | exact resolve eq743497 eq30567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30567 eq743497
  have eq743704 : (k (M.op (M.op x y) (σ x)) (M.op (M.op x y) (σ x))) = (M.op y (M.op (M.op (M.op x y) (σ x)) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq743537 eq188
    | exact resolve eq188 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq743537
  have eq744469 : (k (M.op (M.op x y) (σ x)) (M.op (M.op x y) (σ x))) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq743704
       have i₂ := eq3119 y sF0 sF2
       grind)
    | exact superpose eq3119 eq743704
    | exact resolve eq743704 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119 eq743704
  have eq744615 : (k (M.op (M.op x y) (σ x)) (M.op (M.op x y) (σ x))) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq744469
       have i₂ := eq3797 y sF0
       grind)
    | exact superpose eq3797 eq744469
    | exact resolve eq744469 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797 eq744469
  have eq744750 : (M.op y (M.op x y)) = (k (M.op (M.op x y) (σ x)) (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq83399 eq744615
    | exact resolve eq744615 eq83399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83399 eq744615
  have eq744868 : (M.op (M.op x y) (k (M.op x y) (M.op x y))) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq744750
       have i₂ := eq700121 sF0 sF2
       grind)
    | exact superpose eq700121 eq744750
    | exact resolve eq744750 eq700121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700121 eq744750
  have eq744968 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq212 eq744868
    | exact resolve eq744868 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744868
  have eq745147 : (M.op (M.op x y) (k (M.op x y) (M.op x y))) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq744968 eq195
    | exact resolve eq195 eq744968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq744968
  have eq745874 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq212 eq745147
    | exact resolve eq745147 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq745147
  have eq745994 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq126553 eq745874
    | exact resolve eq745874 eq126553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126553 eq745874
  have eq746446 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq745994 eq41
    | exact resolve eq41 eq745994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq745994
  have eq746546 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq746446
    | exact resolve eq746446 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746446
  have eq746549 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq126572 eq746546
    | exact resolve eq746546 eq126572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746546
  have eq750509 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq746549 eq1422
    | exact resolve eq1422 eq746549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq750618 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq750509
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq750509
    | exact resolve eq750509 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750509
  have eq750625 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1655 eq750618
    | exact resolve eq750618 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq750618
  have eq750628 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq746549 eq750625
    | exact resolve eq750625 eq746549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746549 eq750625
  have eq750641 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq750628 eq2545
    | exact resolve eq2545 eq750628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq750806 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq750641
  have eq750879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq750806 eq69513
    | exact resolve eq69513 eq750806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69513 eq750806
  have eq750894 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq750879
  have eq750909 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq750894
    | exact resolve eq750894 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750894
  have eq750910 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq750909
  have eq750916 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq750628 eq750910
    | exact resolve eq750910 eq750628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750628 eq750910
  have eq750917 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq750916
  have eq750921 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq750917 eq27
    | exact resolve eq27 eq750917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750917
  have eq751075 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq750921
       have r₂ := eq126572
       grind)
    | exact resolve eq750921 eq126572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126572 eq750921
  have eq751082 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq751075 eq31
    | exact resolve eq31 eq751075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq751075
  have eq751135 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq751082
    | exact resolve eq751082 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq751082
  have eq751136 : x = y := by grind
  clear eq751135
  have eq751152 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq751136
       grind)
    | exact superpose eq751136 eq18
    | exact resolve eq18 eq751136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq751153 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq751136
       grind)
    | exact superpose eq751136 eq24
    | exact resolve eq24 eq751136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq751136
  have eq751159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq751153
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq751153
    | exact resolve eq751153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751153
  have eq751160 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq751152
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq751152
    | exact resolve eq751152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751152
  have eq751161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq751159 eq26
    | exact resolve eq26 eq751159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq751159
  have eq751203 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751161
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq751161
    | exact resolve eq751161 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq751161
  have eq751212 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq751160
       grind)
    | exact superpose eq751160 eq39
    | exact resolve eq39 eq751160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq751160
  have eq751271 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751212
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq751212
    | exact resolve eq751212 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq751212
  have eq751275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq751203 eq751271
    | exact resolve eq751271 eq751203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751203 eq751271
  have eq751277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq751275
    | exact resolve eq751275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq751275
  have eq751279 : False := by grind
  exact eq751279

/-- `Equation4452`: `x ◇ (y ◇ x) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pxy_Equation4452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X0) := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X0 X0)
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (k X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 x X3
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 x
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq198 eq16
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq182 eq209
    | exact resolve eq209 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq209
  have eq211 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq198 eq210
    | exact resolve eq210 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq606 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X2 X0 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq683 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq183
    | exact resolve eq183 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : (M.op (M.op x y) y) = (M.op (k y y) y) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq184 y x
       grind)
    | exact superpose eq184 eq181
    | exact resolve eq181 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq802 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq185 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq185
    | exact resolve eq185 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : (M.op (σ y) (M.op (σ x) (σ y))) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq211 eq13
    | (have j0 := eq13 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
       have r₂ := eq211
       grind)
    | exact resolve eq13 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq916 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by grind
  clear eq911
  have eq935 : x ≠ (M.op x y) ∨ (k y x) = (k y y) := by
    first
    | (have i₁ := eq916
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq916
    | exact resolve eq916 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq940 : (k (σ y) (σ y)) = (k (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq926
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq926
    | exact resolve eq926 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq981 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 X1) X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 (M.op X0 X1) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X1) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : (τ (k (σ y) (σ y))) = (k y (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq940 eq108
    | exact resolve eq108 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq940
  have eq1061 : (k y y) = (k y (τ (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq116 eq1060
    | exact resolve eq1060 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1661 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X2 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have i₂ := eq180 X0 X2 X1
       grind)
    | exact superpose eq180 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X2 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X2 X0))
       have r₂ := eq180 X0 X2 X2
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1687 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq1661 X0 x X2
       grind)
    | (have r₁ := eq1661 X0 x X2
       have r₂ := eq183 X0 x X2
       grind)
    | (have r₁ := eq1661 X0 X2 x
       have r₂ := eq183 X0 x X2
       grind)
    | exact resolve eq1661 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1661
  have eq1751 : ∀ X0 X2 : G, (k X0 X0) = (k X0 (M.op X0 (M.op X2 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1687 X0 X2
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq1687
    | exact resolve eq1687 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1811 : ∀ X0 X1 : G, (k X1 X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1751 X1 x
       have i₂ := eq16 X1 x X0
       grind)
    | exact superpose eq16 eq1751
    | exact resolve eq1751 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2079 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq41
    | exact resolve eq41 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq2080 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2079
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2079
    | exact resolve eq2079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2082 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2080
    | exact resolve eq2080 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2082 eq1011
    | exact resolve eq1011 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2533 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2526
       have r₂ := eq27
       grind)
    | exact resolve eq2526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq2538 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2533
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2533
       grind)
    | exact resolve eq13 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2548 : (M.op (σ y) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq606
    | exact resolve eq606 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq2549 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2533 eq609
    | exact resolve eq609 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq2550 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq683
    | exact resolve eq683 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2551 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2533 eq686
    | exact resolve eq686 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq2553 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq1811
    | exact resolve eq1811 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq2539
  have eq2555 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq2538
  have eq2557 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq2553
    | exact resolve eq2553 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2559 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq2551
    | (have j0 := eq2551 X0
       grind)
    | exact resolve eq2551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq2560 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2550
    | exact resolve eq2550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2561 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq2549
    | (have j0 := eq2549 X0
       grind)
    | exact resolve eq2549 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq2562 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2548
       have i₂ := eq802 sF2
       grind)
    | exact superpose eq802 eq2548
    | exact resolve eq2548 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2571 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | (have r₁ := eq2554
       have r₂ := eq28 (k (σ x) (σ y)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq2554
       have r₂ := eq28 (M.op (σ x) (σ x)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq2554
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq2554 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2572 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2555
    | exact resolve eq2555 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2574 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2082 eq2557
    | exact resolve eq2557 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2575 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2559 x
       have i₂ := eq683 sF2 x
       grind)
    | exact superpose eq683 eq2559
    | exact resolve eq2559 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559
  have eq2576 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2561 x
       have i₂ := eq185 sF2 x
       grind)
    | exact superpose eq185 eq2561
    | exact resolve eq2561 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2577 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2560 eq2562
    | exact resolve eq2562 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2585 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2571
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq2571
    | exact resolve eq2571 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2586 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2560 eq2575
    | exact resolve eq2575 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2587 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2560 eq2576
    | exact resolve eq2576 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2588 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2533 eq2577
    | exact resolve eq2577 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2591 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2082 eq2585
    | exact resolve eq2585 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082 eq2585
  have eq2742 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2591 eq98
    | exact resolve eq98 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2746 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2591 eq802
    | exact resolve eq802 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2751 : (M.op x y) = (k x x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2742
    | exact resolve eq2742 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2742
  have eq2759 : (M.op x (M.op x y)) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq802 x
       have i₂ := eq2751
       grind)
    | exact superpose eq2751 eq802
    | exact resolve eq802 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2780 : (M.op y x) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq185 x y
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq185
    | exact resolve eq185 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2783 : (M.op x y) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq683
    | exact resolve eq683 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2786 : (k x x) = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1751 x y
       have i₂ := eq2588
       grind)
    | exact superpose eq2588 eq1751
    | exact resolve eq1751 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2792 : (k x x) = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2786
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2786
    | exact resolve eq2786 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2795 : (M.op x y) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2783
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2783
    | exact resolve eq2783 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2798 : y = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2588 eq2780
    | exact resolve eq2780 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780
  have eq2811 : (M.op x y) = (M.op x (k x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2792 eq2795
    | exact resolve eq2795 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2814 : y = (M.op x (k x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2792 eq2798
    | exact resolve eq2798 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792 eq2798
  have eq2826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2811 eq2814
    | exact resolve eq2814 eq2811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811 eq2814
  have eq2843 : (k y y) = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2826 eq1061
    | exact resolve eq1061 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq2826
  have eq2844 : (k y y) = (k y (τ (k (σ y) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2843
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq2843
    | exact resolve eq2843 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2848 : (k y y) = (k y (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq2844
    | exact resolve eq2844 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq2844
  have eq3161 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2574 eq184
    | exact resolve eq184 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq3162 : (M.op (σ x) (k (σ x) (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3161 x
       have i₂ := eq683 sF2 x
       grind)
    | exact superpose eq683 eq3161
    | exact resolve eq3161 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq3166 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2560 eq3162
    | exact resolve eq3162 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560 eq3162
  have eq3169 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2588 eq3166
    | exact resolve eq3166 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166
  have eq3352 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq3169 eq2746
    | exact resolve eq2746 eq3169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746 eq3169
  have eq3370 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq3352
  have eq5234 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2572 eq142
    | exact resolve eq142 eq2572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq5239 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq5234
    | exact resolve eq5234 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq5244 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2588 eq5239
    | exact resolve eq5239 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5239
  have eq5245 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq5244
  have eq5509 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq981 y x X0
       have i₂ := eq5245
       grind)
    | exact superpose eq5245 eq981
    | (have j0 := eq981 x y x
       grind)
    | exact resolve eq981 eq5245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5624 : ∀ X0 : G, (M.op y x) = (M.op x (M.op X0 x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq5509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5672 : (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5624 x
       have i₂ := eq683 x x
       grind)
    | exact superpose eq683 eq5624
    | exact resolve eq5624 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624
  have eq5725 : x = (M.op x y) ∨ (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5672
    | exact resolve eq5672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5672
  have eq5754 : x = (M.op x y) ∨ (M.op y x) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2751 eq5725
    | exact resolve eq5725 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751 eq5725
  have eq5762 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2759 eq5754
    | exact resolve eq5754 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5754
  have eq7133 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2587 eq1001
    | (have j0 := eq1001 X0 (σ x) x
       grind)
    | exact resolve eq1001 eq2587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq2587
  have eq7302 : ∀ X0 : G, (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq7133 x
       have i₂ := eq683 sF2 x
       grind)
    | exact superpose eq683 eq7133
    | (have j0 := eq7133 X0
       grind)
    | exact resolve eq7133 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7133
  have eq7395 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2574 eq7302
    | (have j0 := eq7302 X0
       grind)
    | exact resolve eq7302 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574 eq7302
  have eq7450 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2586 eq7395
    | (have j0 := eq7395 X0
       grind)
    | exact resolve eq7395 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586 eq7395
  have eq7478 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2588 eq7450
    | (have j0 := eq7450 X0
       grind)
    | exact resolve eq7450 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq7450
  have eq7493 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3370 eq7478
    | (have j0 := eq7478 X0
       grind)
    | exact resolve eq7478 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370 eq7478
  have eq7494 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq7493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq8148 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq5762
       grind)
    | exact superpose eq5762 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq5762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8172 : y ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq5762
  have eq8173 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq8148
  have eq8179 : x = (M.op x y) ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8173
    | exact resolve eq8173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq8180 : x = (M.op x y) ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq8179
  have eq8185 : x = (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq5245 eq8180
    | exact resolve eq8180 eq5245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245 eq8180
  have eq8187 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8185
       have r₂ := eq8172
       grind)
    | exact resolve eq8185 eq8172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8172 eq8185
  have eq8193 : y ≠ y ∨ (k x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq8187
       grind)
    | exact superpose eq8187 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8187
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8187
       grind)
    | exact resolve eq13 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8204 : (M.op y x) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq185 x y
       have i₂ := eq8187
       grind)
    | exact superpose eq8187 eq185
    | exact resolve eq185 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq8207 : (M.op x y) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq8187
       grind)
    | exact superpose eq8187 eq683
    | exact resolve eq683 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8214 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1751 x y
       have i₂ := eq8187
       grind)
    | exact superpose eq8187 eq1751
    | exact resolve eq1751 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8216 : (k x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8193
  have eq8223 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8214
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8214
    | exact resolve eq8214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8214
  have eq8230 : (M.op x y) = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8207
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8207
    | exact resolve eq8207 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207
  have eq8233 : y = (M.op x (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8187 eq8204
    | exact resolve eq8204 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8244 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq28 x y
       grind)
    | (have r₁ := eq8216
       have r₂ := eq28 (k x y) (M.op x x)
       grind)
    | (have r₁ := eq8216
       have r₂ := eq28 (M.op x x) (k x y)
       grind)
    | (have r₁ := eq8216
       have r₂ := eq28 x y
       grind)
    | exact resolve eq8216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8253 : (M.op x y) = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8223 eq8230
    | exact resolve eq8230 eq8223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8230
  have eq8256 : y = (M.op x (k x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8223 eq8233
    | exact resolve eq8233 eq8223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8233
  have eq8266 : (k x x) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8244
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq8244
    | exact resolve eq8244 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8244
  have eq8272 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8253 eq8256
    | exact resolve eq8256 eq8253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8253 eq8256
  have eq8297 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8272 eq32
    | exact resolve eq32 eq8272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8306 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8272 eq153
    | exact resolve eq153 eq8272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq8323 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq142 eq8306
    | exact resolve eq8306 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8306
  have eq8332 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq8297
    | exact resolve eq8297 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8297
  have eq8333 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq8332
  have eq8336 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8333
       grind)
    | exact superpose eq8333 eq18
    | exact resolve eq18 eq8333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8337 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8333
       grind)
    | exact superpose eq8333 eq24
    | exact resolve eq24 eq8333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8375 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8337
    | exact resolve eq8337 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8337
  have eq8541 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8336 eq2759
    | exact resolve eq2759 eq8336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq8570 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8541
  have eq8590 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8333 eq8570
    | exact resolve eq8570 eq8333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8570
  have eq8591 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq8590
  have eq8612 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8591 eq11
    | (have j0 := eq11 (M.op x y) (k (M.op x y) x)
       grind)
    | exact resolve eq11 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8613 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8591 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq8591
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8591
       grind)
    | exact resolve eq13 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8627 : (M.op x (k x x)) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8591 eq683
    | exact resolve eq683 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8635 : (k x x) = (k x (M.op (M.op x y) x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8591 eq1811
    | exact resolve eq1811 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq8636 : (k x (M.op x y)) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq8613
  have eq8637 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq8612
  have eq8646 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8591 eq8635
    | exact resolve eq8635 eq8591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8591 eq8635
  have eq8654 : (M.op x y) = (M.op x (k x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8336 eq8627
    | exact resolve eq8627 eq8336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8627
  have eq8668 : (k x (M.op x y)) = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq28 x (M.op x y)
       grind)
    | (have r₁ := eq8636
       have r₂ := eq28 (k x (M.op x y)) (M.op x x)
       grind)
    | (have r₁ := eq8636
       have r₂ := eq28 (M.op x x) (k x (M.op x y))
       grind)
    | (have r₁ := eq8636
       have r₂ := eq28 x y
       grind)
    | exact resolve eq8636 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8636
  have eq8669 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8336 eq8637
    | exact resolve eq8637 eq8336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8336 eq8637
  have eq8670 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8669
  have eq8681 : (M.op x y) = (M.op x (k x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8646 eq8654
    | exact resolve eq8654 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8654
  have eq8694 : (k x x) = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq8668
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq8668
    | exact resolve eq8668 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8668
  have eq8759 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8670 eq40
    | exact resolve eq40 eq8670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8670
  have eq8765 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq8759
    | exact resolve eq8759 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8759
  have eq8768 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8375 eq8765
    | exact resolve eq8765 eq8375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8765
  have eq8779 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8768 eq981
    | (have j0 := eq981 (M.op (σ y) (σ x)) (M.op (σ x) (M.op X0 (σ x))) x
       grind)
    | exact resolve eq981 eq8768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq8783 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8779 x
       have i₂ := eq683 sF2 x
       grind)
    | exact superpose eq683 eq8779
    | exact resolve eq8779 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8779
  have eq8787 : (M.op (σ y) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq8783
    | exact resolve eq8783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq8796 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq8266
       grind)
    | exact superpose eq8266 eq41
    | exact resolve eq41 eq8266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8266
  have eq8801 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8796
    | exact resolve eq8796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796
  have eq8803 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8801
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq8801
    | exact resolve eq8801 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8801
  have eq8805 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8803
    | exact resolve eq8803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8803
  have eq8810 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8805 eq1011
    | exact resolve eq1011 eq8805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq8805
  have eq8817 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8810
  have eq9865 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8817 eq98
    | exact resolve eq98 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq10494 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8694
       have i₂ := eq9865
       grind)
    | exact superpose eq9865 eq8694
    | exact resolve eq8694 eq9865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694
  have eq10498 : (M.op x (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq802 x
       have i₂ := eq9865
       grind)
    | exact superpose eq9865 eq802
    | exact resolve eq802 eq9865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq10965 : (k y x) = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq8323
    | exact resolve eq8323 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8323
  have eq10971 : (k y x) = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10965
       have r₂ := eq935
       grind)
    | exact resolve eq10965 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq10965
  have eq10972 : (k y y) = (k y (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq8333 eq10971
    | exact resolve eq10971 eq8333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10971
  have eq10978 : (M.op (M.op x y) y) = (M.op (k y (M.op x y)) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq753
       have i₂ := eq10972
       grind)
    | exact superpose eq10972 eq753
    | exact resolve eq753 eq10972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq10979 : (k y (M.op x y)) = (k y (k y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2848
       have i₂ := eq10972
       grind)
    | exact superpose eq10972 eq2848
    | exact resolve eq2848 eq10972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq10995 : (k y (M.op x y)) = (k y (k y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq10979
  have eq13552 : (k x x) = (k x (M.op x (M.op x (τ (M.op (σ x) (σ y)))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10498 eq1751
    | exact resolve eq1751 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq13561 : (τ (M.op (σ x) (σ y))) = (k x (M.op x (M.op x (τ (M.op (σ x) (σ y)))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9865 eq13552
    | exact resolve eq13552 eq9865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9865 eq13552
  have eq13929 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10494 eq8681
    | exact resolve eq8681 eq10494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8681 eq10494
  have eq13959 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq13929
  have eq17049 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8817 eq8787
    | exact resolve eq8787 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq17093 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17049
  have eq20348 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 (σ x))) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7494 eq142
    | (have j1 := eq7494 X0
       grind)
    | exact resolve eq142 eq7494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq7494
  have eq20371 : ∀ X0 : G, y = (k (τ (M.op X0 (σ x))) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq32 eq20348
    | (have j0 := eq20348 X0
       grind)
    | exact resolve eq20348 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20348
  have eq20390 : ∀ X0 : G, y = (k (τ (M.op X0 (σ x))) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq8187 eq20371
    | (have j0 := eq20371 X0
       grind)
    | exact resolve eq20371 eq8187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187 eq20371
  have eq31264 : y = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq2533 eq20390
    | exact resolve eq20390 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533 eq20390
  have eq31288 : y = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq31264
  have eq31304 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq31288
    | exact resolve eq31288 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31288
  have eq31386 : (M.op (M.op x y) y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq31304 eq10978
    | exact resolve eq10978 eq31304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10978
  have eq31388 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq31304 eq10995
    | exact resolve eq10995 eq31304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10995 eq31304
  have eq31426 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq31388
  have eq31428 : (M.op (M.op x y) y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq31386
  have eq31442 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq8272 eq31426
    | exact resolve eq31426 eq8272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8272 eq31426
  have eq31444 : (k y y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31428
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq31428
    | exact resolve eq31428 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31428
  have eq31449 : y = (M.op (M.op x y) y) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq188 eq31442
    | exact resolve eq31442 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31442
  have eq31451 : (k y y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq8333 eq31444
    | exact resolve eq31444 eq8333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8333 eq31444
  have eq31454 : y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq10972 eq31449
    | exact resolve eq31449 eq10972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31449
  have eq31456 : y = (M.op (M.op x y) y) ∨ (k y y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq188 eq31451
    | exact resolve eq31451 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq31451
  have eq31460 : y = (M.op (M.op x y) y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10972 eq31456
    | exact resolve eq31456 eq10972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10972 eq31456
  have eq31464 : y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31454 eq31460
    | exact resolve eq31460 eq31454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31454 eq31460
  have eq31465 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq31464
  have eq59893 : (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq17093 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59930 : (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17093
  have eq59931 : (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq59893
  have eq59982 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq59931
    | exact resolve eq59931 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59931
  have eq59983 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq59982
  have eq60013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq8768 eq59983
    | exact resolve eq59983 eq8768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8768 eq59983
  have eq60038 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq60013
       have r₂ := eq59930
       grind)
    | exact resolve eq60013 eq59930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59930 eq60013
  have eq60091 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60038 eq683
    | exact resolve eq683 eq60038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq60139 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq60091
    | exact resolve eq60091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60091
  have eq60592 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60139 eq8787
    | exact resolve eq8787 eq60139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8787 eq60139
  have eq60634 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq60592
  have eq60666 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60038 eq60634
    | exact resolve eq60634 eq60038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60038 eq60634
  have eq60757 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60666 eq27
    | exact resolve eq27 eq60666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60666
  have eq60897 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq60757
       have r₂ := eq8375
       grind)
    | exact resolve eq60757 eq8375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8375 eq60757
  have eq60905 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60897 eq198
    | exact resolve eq198 eq60897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq60966 : (τ (σ x)) = (k x (M.op x (M.op x (τ (σ x))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60897 eq13561
    | exact resolve eq13561 eq60897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13561
  have eq60972 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60897 eq13959
    | exact resolve eq13959 eq60897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13959
  have eq61003 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq60972
  have eq61009 : (τ (σ x)) = (k x (M.op x (M.op x (τ (σ x))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq60966
  have eq61072 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq30 eq61003
    | exact resolve eq61003 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61003
  have eq61077 : x = (k x (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq61009
    | exact resolve eq61009 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61009
  have eq61110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq60905
    | exact resolve eq60905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60905
  have eq61113 : (M.op x y) = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61072
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq61072
    | exact resolve eq61072 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61072
  have eq61118 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq61077
       have i₂ := eq1751 x x
       grind)
    | exact superpose eq1751 eq61077
    | exact resolve eq61077 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq61077
  have eq61141 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq60897 eq61110
    | exact resolve eq61110 eq60897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60897 eq61110
  have eq61142 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq8646 eq61113
    | exact resolve eq61113 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8646 eq61113
  have eq61145 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8223 eq61118
    | exact resolve eq61118 eq8223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8223 eq61118
  have eq61166 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq61141 eq61142
    | exact resolve eq61142 eq61141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61142
  have eq61167 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq61166
  have eq61170 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61141 eq61145
    | exact resolve eq61145 eq61141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61141 eq61145
  have eq61171 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq61170
  have eq61200 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61167 eq61171
    | exact resolve eq61171 eq61167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61167 eq61171
  have eq61201 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq61200
  have eq61226 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61201 eq32
    | exact resolve eq32 eq61201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61201
  have eq61296 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq61226
    | exact resolve eq61226 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61226
  have eq61297 : x = (M.op x y) ∨ x = y := by grind
  clear eq61296
  have eq61316 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq61297
       grind)
    | exact superpose eq61297 eq18
    | exact resolve eq18 eq61297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61883 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61316 eq31465
    | exact resolve eq31465 eq61316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31465 eq61316
  have eq61958 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq61883
  have eq62034 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq61958 eq32
    | exact resolve eq32 eq61958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq61958
  have eq62104 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq62034
    | exact resolve eq62034 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62034
  have eq62105 : y = (M.op x y) ∨ x = y := by grind
  clear eq62104
  have eq62197 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq62105
  have eq62202 : x = y := by
    first
    | (have r₁ := eq62197
       have r₂ := eq61297
       grind)
    | exact resolve eq62197 eq61297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61297 eq62197
  have eq62222 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq62202
       grind)
    | exact superpose eq62202 eq18
    | exact resolve eq18 eq62202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq62202
       grind)
    | exact superpose eq62202 eq24
    | exact resolve eq24 eq62202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq62202
  have eq62254 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62223
    | exact resolve eq62223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62223
  have eq62255 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq62222
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq62222
    | exact resolve eq62222 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62222
  have eq62258 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62254 eq26
    | exact resolve eq26 eq62254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq62254
  have eq62315 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq62258
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq62258
    | exact resolve eq62258 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq62258
  have eq62334 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq62255
       grind)
    | exact superpose eq62255 eq40
    | exact resolve eq40 eq62255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq62255
  have eq62340 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq62334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62334
    | exact resolve eq62334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq62334
  have eq62343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62315 eq62340
    | exact resolve eq62340 eq62315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62315 eq62340
  have eq62345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq62343
    | exact resolve eq62343 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq62343
  have eq62347 : False := by grind
  exact eq62347
