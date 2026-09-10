import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_x_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq224 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq250 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq224
    | (have j0 := eq224 X0 X1
       grind)
    | exact resolve eq224 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq224
  have eq254 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq250 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq250 (σ (M.op X0 X0)) X0
       have r₂ := eq76 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq250 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq362 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq254
    | exact resolve eq254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq254 (σ X0) X1
       grind)
    | exact superpose eq254 eq15
    | (have j1 := eq254 (σ X0) X1
       grind)
    | exact resolve eq15 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq391 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq362 (τ X1) X0
       grind)
    | exact superpose eq362 eq18
    | (have j1 := eq362 (τ X1) X0
       grind)
    | exact resolve eq18 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq823 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq391
    | exact resolve eq391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq823
    | (have j0 := eq823 X0 X1
       grind)
    | exact resolve eq823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1363 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq372 x y
       grind)
    | exact superpose eq372 eq16
    | (have j1 := eq372 x y
       grind)
    | exact resolve eq16 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1387 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq4515 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1363
       have i₂ := eq876 y x
       grind)
    | exact superpose eq876 eq1363
    | (have j1 := eq876 (σ y) (σ x)
       grind)
    | (have r₁ := eq1363
       have r₂ := eq876 y x
       grind)
    | exact resolve eq1363 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq4516 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4515
  have eq4520 : x ≠ x ∨ x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4516
       grind)
    | exact superpose eq4516 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4516
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4516
       grind)
    | exact resolve eq13 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4521 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq4520
  have eq13096 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq4521
       grind)
    | exact superpose eq4521 eq76
    | exact resolve eq76 eq4521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13098 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4521
       grind)
    | exact superpose eq4521 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4521
       grind)
    | exact resolve eq13 eq4521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq13099 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq13098
  have eq13100 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13099
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13099
    | exact resolve eq13099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13099
  have eq13101 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13096
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13096
    | exact resolve eq13096 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13096
  have eq13104 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13100
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq13100
    | exact resolve eq13100 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq13100
  have eq13105 : x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq13104
       have r₂ := eq13101
       grind)
    | exact resolve eq13104 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq13104
  have eq13300 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13105
       have i₂ := eq362 y x
       grind)
    | exact superpose eq362 eq13105
    | (have j1 := eq362 y x
       grind)
    | exact resolve eq13105 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq13320 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1387 x y
       have i₂ := eq13105
       grind)
    | exact superpose eq13105 eq1387
    | (have j0 := eq1387 x y
       grind)
    | (have r₁ := eq1387 x y
       have r₂ := eq13105
       grind)
    | exact resolve eq1387 eq13105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13105
  have eq13329 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq13320
  have eq13335 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13300
  have eq13336 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq1387 x y
       grind)
    | (have r₁ := eq13329
       have r₂ := eq1387 x y
       grind)
    | exact resolve eq13329 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13329
  have eq13491 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13336
       grind)
    | exact superpose eq13336 eq16
    | exact resolve eq16 eq13336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13336
  have eq14312 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13491
       have i₂ := eq13335
       grind)
    | exact superpose eq13335 eq13491
    | (have r₁ := eq13491
       have r₂ := eq13335
       grind)
    | exact resolve eq13491 eq13335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13335
  have eq14322 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq14312
  have eq14323 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq14322
  have eq14327 : x = (M.op y y) := by
    first
    | (have r₁ := eq14323
       have r₂ := eq13491
       grind)
    | exact resolve eq14323 eq13491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13491 eq14323
  have eq14476 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq14327
       grind)
    | exact superpose eq14327 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15669 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14476 x
       have i₂ := eq4516
       grind)
    | exact superpose eq4516 eq14476
    | (have r₁ := eq14476 x
       have r₂ := eq4516
       grind)
    | exact resolve eq14476 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516 eq14476
  have eq15674 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15669
  have eq17938 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1387 x y
       have i₂ := eq15674
       grind)
    | exact superpose eq15674 eq1387
    | (have j0 := eq1387 x y
       grind)
    | exact resolve eq1387 eq15674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq15674
  have eq17947 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17938
  have eq17948 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17947
  have eq18169 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17948
       grind)
    | exact superpose eq17948 eq16
    | exact resolve eq16 eq17948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18174 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq17948
       grind)
    | exact superpose eq17948 eq76
    | exact resolve eq76 eq17948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq17948
  have eq18179 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18174
       have i₂ := eq14327
       grind)
    | exact superpose eq14327 eq18174
    | exact resolve eq18174 eq14327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14327 eq18174
  have eq18180 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq18179
  have eq18184 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq18180
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18180
    | exact resolve eq18180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18180
  have eq18219 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq876 y x
       have i₂ := eq18184
       grind)
    | exact superpose eq18184 eq876
    | (have j0 := eq876 y x
       grind)
    | exact resolve eq876 eq18184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq18184
  have eq18324 : x = (M.op x y) := by
    first
    | (have r₁ := eq18219
       have r₂ := eq18169
       grind)
    | exact resolve eq18219 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18219
  have eq18544 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18169
       have i₂ := eq18324
       grind)
    | exact superpose eq18324 eq18169
    | exact resolve eq18169 eq18324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18169 eq18324
  have eq18556 : False := by grind
  exact eq18556

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op (M.op (M.op X1 X0) (M.op X1 X2)) (M.op X0 (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X1 X3 : G, (M.op X3 (M.op (M.op X1 X3) X1)) = X3 := by
    intro X1 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op x X1) (M.op x x))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X0)) = (M.op (M.op (M.op X2 X1) (M.op X2 X0)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 X1 (M.op (M.op X2 X1) (M.op X2 X0))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X0) X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X2 X0)) X1) = (M.op (M.op (M.op X2 X1) (M.op X2 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X2 X0)) X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) (M.op X2 X0)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k (M.op (M.op X0 X1) X0) X1) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) X0) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 x) X1) x
       have r₂ := eq45 X1 x
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) X1) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 X2 : G, (k (M.op (M.op X2 X1) (M.op X2 X0)) X1) = (M.op (M.op (M.op X2 X1) (M.op X2 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq70 : ∀ X0 X1 : G, (k (τ (M.op (M.op X0 X1) X0)) (τ X1)) = (τ (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (M.op (M.op X0 X1) X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq23
    | exact resolve eq23 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq106 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq23
    | exact resolve eq23 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq110 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq110
    | exact resolve eq110 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq107 (τ X0)
       grind)
    | exact superpose eq107 eq109
    | exact resolve eq109 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq15
    | (have j1 := eq108 X0 X1
       grind)
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124 x y
       grind)
    | exact superpose eq124 eq16
    | (have j1 := eq124 x y
       grind)
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq142 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq108 (σ x) (σ y)
       grind)
    | exact superpose eq108 eq129
    | (have j1 := eq108 x y
       grind)
    | (have r₁ := eq129
       have r₂ := eq108 (σ x) (σ y)
       grind)
    | exact resolve eq129 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq129
  have eq143 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq142
  have eq155 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq143
       grind)
    | exact superpose eq143 eq111
    | exact resolve eq111 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq159 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq155
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq155
    | exact resolve eq155 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq160 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq159
  have eq164 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (M.op (σ x) (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq9
    | exact resolve eq9 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq112 (σ y)
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq112
    | exact resolve eq112 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq160
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq160
       grind)
    | exact resolve eq13 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq173
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq173
    | exact resolve eq173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq182 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq179
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq179
    | exact resolve eq179 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq179
  have eq183 : ∀ X0 : G, y = (M.op y (M.op (M.op x x) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq9
    | exact resolve eq9 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq9
    | exact resolve eq9 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op y X0) ∨ (M.op y X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq182
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq182
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq182
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : y = (M.op y (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq183
    | exact resolve eq183 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq330 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq164 (σ y)
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq164
    | exact resolve eq164 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq374 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 (M.op X1 X3)) (M.op (M.op X2 X1) (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X3)) (M.op (M.op X2 X1) (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 X2) (M.op X0 X1))) (σ X2)) = (σ (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op (M.op X0 X2) (M.op X0 X1)) X2
       have i₂ := eq53 X1 X2 X0
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq756 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X3)) = (M.op (M.op X1 (M.op X1 X3)) (M.op (M.op (M.op X2 X1) (M.op X2 X0)) (M.op (M.op (M.op X2 X1) (M.op X2 X0)) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq44 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X0 X1)) = (M.op (M.op (M.op X0 y) (M.op X0 X1)) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 y X0
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq46
    | exact resolve eq46 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq46 X1 X0 X0
       grind)
    | exact superpose eq46 eq45
    | exact resolve eq45 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq46
  have eq1064 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op (M.op X1 (M.op X0 X0)) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1016 X0 X0
       grind)
    | exact superpose eq1016 eq49
    | exact resolve eq49 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1016
  have eq1205 : ∀ X0 X1 X2 X3 : G, (k (σ (M.op X1 (M.op X1 X3))) (σ (M.op (M.op X2 X1) (M.op X2 X0)))) = (σ (M.op (M.op X1 (M.op X1 X3)) (M.op (M.op X2 X1) (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq401 X0 X1 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq401
    | exact resolve eq401 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1064 (M.op X1 x) x
       have i₂ := eq9 x X1 x
       grind)
    | exact superpose eq9 eq1064
    | exact resolve eq1064 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 : G, (τ (M.op (M.op X1 (M.op X0 X0)) X1)) = (k (τ (M.op (M.op X1 (M.op X0 X0)) X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op X0 X0)
       have i₂ := eq1064 X0 X1
       grind)
    | exact superpose eq1064 eq70
    | exact resolve eq70 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1064
  have eq1384 : ∀ X0 X1 : G, (τ (M.op (M.op X1 (M.op X0 X0)) X1)) = (k (τ (M.op (M.op X1 (M.op X0 X0)) X1)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357 X0 X1
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq1357
    | exact resolve eq1357 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1576 : (M.op y x) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have j0 := eq195 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1582 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq1576
       grind)
    | exact superpose eq1576 eq15
    | exact resolve eq15 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1598 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq196 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1604 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq1598
       grind)
    | exact superpose eq1598 eq15
    | exact resolve eq15 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1612 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1604
       grind)
    | exact superpose eq1604 eq16
    | exact resolve eq16 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5162 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X1 (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq756 X1 X1 X0 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq1340 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq1340 eq756
    | exact resolve eq756 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq1340
  have eq5361 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op y (M.op y X0)) (M.op (M.op x x) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq5162 y y x
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq5162
    | exact resolve eq5162 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9193 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (M.op (τ (M.op X1 X0)) (τ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1384 (M.op X1 x) x
       have i₂ := eq9 x X1 x
       grind)
    | exact superpose eq9 eq1384
    | exact resolve eq1384 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq9277 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (M.op (τ (M.op X1 X0)) (τ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9193 X0 X1
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq9193
    | exact resolve eq9193 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq9193
  have eq9313 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (τ (M.op X1 (σ X0))) (τ (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9277 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9277
    | exact resolve eq9277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9277
  have eq9434 : ∀ X0 : G, (M.op x x) = (k (M.op x x) (M.op (τ (M.op X0 (σ y))) (τ (M.op X0 (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq9313 y x
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq9313
    | exact resolve eq9313 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9313
  have eq17091 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq176 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq17095 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq17091
       grind)
    | exact superpose eq17091 eq1612
    | (have r₁ := eq1612
       have r₂ := eq17091
       grind)
    | exact resolve eq1612 eq17091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17099 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17095
  have eq17107 : (M.op x x) = (k (M.op x x) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9434 (σ x)
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq9434
    | exact resolve eq9434 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq17111 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq9
    | exact resolve eq9 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17113 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17099
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17099
       grind)
    | exact resolve eq12 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17197 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17113
  have eq17219 : (M.op x x) = (k (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17107
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17107
    | exact resolve eq17107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17107
  have eq17225 : x = (M.op x y) ∨ (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq17219
       have i₂ := eq107 (M.op x x)
       grind)
    | exact superpose eq107 eq17219
    | exact resolve eq17219 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17219
  have eq17392 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq17197
       grind)
    | exact superpose eq17197 eq1612
    | exact resolve eq1612 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq17395 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17392
  have eq17505 : (M.op x x) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq1010 x y
       have i₂ := eq17225
       grind)
    | exact superpose eq17225 eq1010
    | exact resolve eq1010 eq17225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010 eq17225
  have eq17533 : (M.op x x) = (M.op (M.op x x) (M.op x x)) := by grind
  clear eq17505
  have eq17571 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq228
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq228
    | exact resolve eq228 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq17579 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op y (M.op y X0)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq5361 X0
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq5361
    | exact resolve eq5361 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5361
  have eq17590 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq9 x x x
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq9
    | exact resolve eq9 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17607 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x (M.op x X0)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq5162 x x X0
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq5162
    | exact resolve eq5162 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq17624 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq111 (M.op x x)
       have i₂ := eq17533
       grind)
    | exact superpose eq17533 eq111
    | exact resolve eq111 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533
  have eq17716 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq17624
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq17624
    | exact resolve eq17624 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq17624
  have eq19439 : ∀ X0 X1 : G, (k (σ (M.op y (M.op x x))) (σ (M.op (M.op X1 y) (M.op X1 X0)))) = (σ (M.op (M.op y (M.op x x)) (M.op (M.op X1 y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 y x y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq1205
    | exact resolve eq1205 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq19444 : ∀ X0 X1 : G, (k (σ x) (σ (M.op (M.op X1 x) (M.op X1 X0)))) = (σ (M.op x (M.op (M.op X1 x) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 x x x
       have i₂ := eq17590
       grind)
    | exact superpose eq17590 eq1205
    | exact resolve eq1205 eq17590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq19700 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op (M.op X1 x) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19444 X0 X1
       have i₂ := eq9 x X1 X0
       grind)
    | exact superpose eq9 eq19444
    | exact resolve eq19444 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19444
  have eq19704 : ∀ X0 X1 : G, (k (σ y) (σ (M.op (M.op X1 y) (M.op X1 X0)))) = (σ (M.op y (M.op (M.op X1 y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19439 X0 X1
       have i₂ := eq17571
       grind)
    | exact superpose eq17571 eq19439
    | exact resolve eq19439 eq17571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17571 eq19439
  have eq19806 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ (M.op (M.op X1 y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19704 X0 X1
       have i₂ := eq9 y X1 X0
       grind)
    | exact superpose eq9 eq19704
    | exact resolve eq19704 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19704
  have eq20967 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq184 (M.op y X0)
       have i₂ := eq17579 X0
       grind)
    | exact superpose eq17579 eq184
    | exact resolve eq184 eq17579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq17579
  have eq21131 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y (M.op y X0)
       have i₂ := eq20967 X0
       grind)
    | exact superpose eq20967 eq9
    | exact resolve eq9 eq20967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21132 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X0) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 y (M.op y X0) x
       have i₂ := eq20967 X0
       grind)
    | exact superpose eq20967 eq44
    | exact resolve eq44 eq20967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq21141 : ∀ X0 : G, (k (σ (M.op y X0)) (σ X0)) = (σ (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq401 y (M.op y X0) X0
       have i₂ := eq20967 X0
       grind)
    | exact superpose eq20967 eq401
    | exact resolve eq401 eq20967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq21159 : (σ x) = (k (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq19700 (M.op y x) y
       have i₂ := eq20967 x
       grind)
    | exact superpose eq20967 eq19700
    | exact resolve eq19700 eq20967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19700 eq20967
  have eq21479 : (σ x) = (k (σ x) (k (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq21159
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq21159
    | exact resolve eq21159 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq21159
  have eq22234 : (M.op y x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq21132 x x
       have i₂ := eq17590
       grind)
    | exact superpose eq17590 eq21132
    | exact resolve eq21132 eq17590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17590 eq21132
  have eq22782 : (σ (M.op y x)) = (k (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq21141 x
       have i₂ := eq22234
       grind)
    | exact superpose eq22234 eq21141
    | exact resolve eq21141 eq22234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21141 eq22234
  have eq22860 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) (M.op x (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x X0) x x
       have i₂ := eq17607 X0
       grind)
    | exact superpose eq17607 eq9
    | exact resolve eq9 eq17607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17607
  have eq23018 : ∀ X0 : G, (M.op X0 (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x (M.op x X0)
       have i₂ := eq22860 X0
       grind)
    | exact superpose eq22860 eq9
    | exact resolve eq9 eq22860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23050 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq19806 (M.op x y) x
       have i₂ := eq22860 y
       grind)
    | exact superpose eq22860 eq19806
    | exact resolve eq19806 eq22860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806 eq22860
  have eq23556 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23050
       have i₂ := eq1604
       grind)
    | exact superpose eq1604 eq23050
    | exact resolve eq23050 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq23050
  have eq29327 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23556
       have i₂ := eq17197
       grind)
    | exact superpose eq17197 eq23556
    | exact resolve eq23556 eq17197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17197 eq23556
  have eq29334 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq29327
  have eq33515 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq330
       have i₂ := eq17716
       grind)
    | exact superpose eq17716 eq330
    | exact resolve eq330 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq33526 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq9 (σ x) (σ x) (σ x)
       have i₂ := eq17716
       grind)
    | exact superpose eq17716 eq9
    | exact resolve eq9 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17716
  have eq33874 : ∀ X0 X1 : G, (k (σ x) (M.op (M.op X1 (σ x)) (M.op X1 X0))) = (M.op (σ x) (M.op (M.op X1 (σ x)) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 (σ x) x (σ x)
       have i₂ := eq33526
       grind)
    | exact superpose eq33526 eq374
    | exact resolve eq374 eq33526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq34017 : ∀ X0 X1 : G, (σ x) = (k (σ x) (M.op (M.op X1 (σ x)) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33874 X0 X1
       have i₂ := eq9 (σ x) X1 X0
       grind)
    | exact superpose eq9 eq33874
    | exact resolve eq33874 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33874
  have eq35142 : (σ x) = (k (σ x) (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq34017 (σ y) (σ y)
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq34017
    | exact resolve eq34017 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34017
  have eq45703 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17111 (σ x)
       have i₂ := eq33526
       grind)
    | exact superpose eq33526 eq17111
    | exact resolve eq17111 eq33526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17111
  have eq45948 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17395
       have i₂ := eq45703
       grind)
    | exact superpose eq45703 eq17395
    | exact resolve eq17395 eq45703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17395
  have eq45950 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29334
       have i₂ := eq45703
       grind)
    | exact superpose eq45703 eq29334
    | exact resolve eq29334 eq45703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29334
  have eq45952 : (σ x) = (k (σ x) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35142
       have i₂ := eq45703
       grind)
    | exact superpose eq45703 eq35142
    | exact resolve eq35142 eq45703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35142 eq45703
  have eq46104 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45950
  have eq46106 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45948
  have eq46159 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45952
       have i₂ := eq33515
       grind)
    | exact superpose eq33515 eq45952
    | exact resolve eq45952 eq33515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45952
  have eq46161 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46104
       have i₂ := eq107 (σ y)
       grind)
    | exact superpose eq107 eq46104
    | exact resolve eq46104 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46104
  have eq46187 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46161
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq46161
    | exact resolve eq46161 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46161
  have eq47352 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46106
       have i₂ := eq17099
       grind)
    | exact superpose eq17099 eq46106
    | exact resolve eq46106 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17099 eq46106
  have eq47353 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq47352
  have eq47355 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21479
       have i₂ := eq46159
       grind)
    | exact superpose eq46159 eq21479
    | exact resolve eq21479 eq46159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479 eq46159
  have eq47361 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47355
       have i₂ := eq107 (σ x)
       grind)
    | exact superpose eq107 eq47355
    | exact resolve eq47355 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq47355
  have eq47486 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47353
       have i₂ := eq46187
       grind)
    | exact superpose eq46187 eq47353
    | exact resolve eq47353 eq46187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46187 eq47353
  have eq47491 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq47486
  have eq76331 : x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq47361
       have r₂ := eq47491
       grind)
    | exact resolve eq47361 eq47491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47361 eq47491
  have eq76368 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23018 y
       have i₂ := eq76331
       grind)
    | exact superpose eq76331 eq23018
    | exact resolve eq23018 eq76331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23018 eq76331
  have eq76558 : y = (M.op y x) := by grind
  clear eq76368
  have eq76642 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq22782
       have i₂ := eq76558
       grind)
    | exact superpose eq76558 eq22782
    | exact resolve eq22782 eq76558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22782
  have eq76693 : x = (M.op x y) := by
    first
    | (have i₁ := eq21131 x
       have i₂ := eq76558
       grind)
    | exact superpose eq76558 eq21131
    | exact resolve eq21131 eq76558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21131 eq76558
  have eq77077 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76693
       grind)
    | exact superpose eq76693 eq16
    | exact resolve eq16 eq76693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76693
  have eq77465 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq17091
       have r₂ := eq77077
       grind)
    | exact resolve eq17091 eq77077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17091
  have eq77474 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77465
       have i₂ := eq76642
       grind)
    | exact superpose eq76642 eq77465
    | exact resolve eq77465 eq76642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76642 eq77465
  have eq77513 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq77474
       grind)
    | exact superpose eq77474 eq9
    | exact resolve eq9 eq77474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77474
  have eq80099 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77513 (σ x)
       have i₂ := eq33515
       grind)
    | exact superpose eq33515 eq77513
    | exact resolve eq77513 eq33515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33515 eq77513
  have eq80373 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq80099
       have i₂ := eq160
       grind)
    | exact superpose eq160 eq80099
    | exact resolve eq80099 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq80099
  have eq80637 : (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77077
       have i₂ := eq80373
       grind)
    | exact superpose eq80373 eq77077
    | exact resolve eq77077 eq80373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77077 eq80373
  have eq80668 : False := by grind
  exact eq80668

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq50 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq50
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq117 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq113 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq113 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq113 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq113
  have eq286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq117 (σ X0) (σ X1)
       grind)
    | exact superpose eq117 eq15
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq286
    | exact resolve eq286 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq286
  have eq296 : False := by grind
  exact eq296

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq631
    | exact resolve eq631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq635 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq632
       have r₂ := eq27
       grind)
    | exact resolve eq632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq637 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq635
    | exact resolve eq635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq639 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq637
    | exact resolve eq637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq666 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq639 eq51
    | (have r₁ := eq51
       have r₂ := eq639
       grind)
    | exact resolve eq51 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq671 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq666
  have eq740 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq671 eq85
    | exact resolve eq85 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq748 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq740
    | exact resolve eq740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq740
  have eq752 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq748
       have r₂ := eq50
       grind)
    | exact resolve eq748 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq755 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq78
    | exact resolve eq78 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq757 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq756
  have eq759 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq757
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq757
    | exact resolve eq757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq760 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq759
  have eq761 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq755
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq755
    | exact resolve eq755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq764 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq760
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq760
    | exact resolve eq760 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq767 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq764 eq27
    | exact resolve eq27 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq764 eq51
    | exact resolve eq51 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq764 eq70
    | (have r₁ := eq70
       have r₂ := eq764
       grind)
    | exact resolve eq70 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq764
  have eq773 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq771
  have eq811 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq761 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq811
  have eq816 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq812
    | exact resolve eq812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq817 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq816
  have eq822 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq824 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq822 eq27
    | exact resolve eq27 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq987 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq773 eq85
    | exact resolve eq85 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq773
  have eq998 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq987
    | exact resolve eq987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq987
  have eq1003 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq998
       have r₂ := eq69
       grind)
    | exact resolve eq998 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1011 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1012 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1011
  have eq1014 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1012
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1012
    | exact resolve eq1012 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1015 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1014
  have eq1020 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1015
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1015
    | exact resolve eq1015 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1015
  have eq1072 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1020 eq104
    | exact resolve eq104 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1081 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1020 eq768
    | (have r₁ := eq768
       have r₂ := eq1020
       grind)
    | exact resolve eq768 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq1020
  have eq1091 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1081
  have eq1092 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1091
  have eq1098 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1072
  have eq1377 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1098 eq1092
    | exact resolve eq1092 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1098
  have eq1381 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1377
  have eq1385 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1381
       have r₂ := eq767
       grind)
    | exact resolve eq1381 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1381
  have eq1387 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1385 eq20
    | exact resolve eq20 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1389 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1385 eq50
    | (have r₁ := eq50
       have r₂ := eq1385
       grind)
    | exact resolve eq50 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1403 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1389
  have eq1414 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1387
    | exact resolve eq1387 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1463 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1414 eq26
    | exact resolve eq26 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1414 eq824
    | (have r₁ := eq824
       have r₂ := eq1414
       grind)
    | exact resolve eq824 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq1491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1483
  have eq1492 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1491
  have eq1513 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1492 eq27
    | exact resolve eq27 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq78
    | exact resolve eq78 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1578 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1572
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1572
    | exact resolve eq1572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1584 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1463 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1463
       grind)
    | exact resolve eq12 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1584
       have r₂ := eq1492
       grind)
    | exact resolve eq1584 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq1584
  have eq1597 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1596
       have r₂ := eq27
       grind)
    | exact resolve eq1596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1650 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1414 eq1578
    | exact resolve eq1578 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq1578
  have eq1672 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1650
  have eq1687 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1672 eq1597
    | exact resolve eq1597 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq1672
  have eq1691 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1687
  have eq1695 : x = (M.op x y) := by
    first
    | (have r₁ := eq1691
       have r₂ := eq1513
       grind)
    | exact resolve eq1691 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq1691
  have eq1749 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1695 eq20
    | exact resolve eq20 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1751 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq1695 eq50
    | exact resolve eq50 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1754 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1695 eq69
    | (have r₁ := eq69
       have r₂ := eq1695
       grind)
    | exact resolve eq69 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1766 : y = (k y x) ∨ x = y := by grind
  clear eq1754
  have eq1779 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1749
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1749
    | exact resolve eq1749 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq1780 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1779 eq26
    | exact resolve eq26 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2328 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq1766
       grind)
    | exact superpose eq1766 eq78
    | exact resolve eq78 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1766
  have eq2337 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1779 eq2328
    | exact resolve eq2328 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2341 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq2337
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2337
    | exact resolve eq2337 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq2351 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2341 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2352 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq2351
  have eq2355 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1780 eq2352
    | exact resolve eq2352 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1780 eq2355
    | exact resolve eq2355 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq2361 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2358
       have r₂ := eq27
       grind)
    | exact resolve eq2358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq2366 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq2361 eq27
    | exact resolve eq27 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2367 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2361 eq51
    | (have r₁ := eq51
       have r₂ := eq2361
       grind)
    | exact resolve eq51 eq2361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2361
  have eq2375 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq2367
  have eq2377 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1779 eq2375
    | exact resolve eq2375 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2540 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2377 eq2341
    | exact resolve eq2341 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2541 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2377 eq117
    | exact resolve eq117 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq2377
  have eq2544 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2540
  have eq2549 : (τ (σ (M.op x y))) = (k y x) ∨ x = y := by
    first
    | exact superpose eq1695 eq2541
    | exact resolve eq2541 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2550 : x = y := by
    first
    | (have r₁ := eq2544
       have r₂ := eq2366
       grind)
    | exact resolve eq2544 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366 eq2544
  have eq2554 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq2549
    | exact resolve eq2549 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2549
  have eq2557 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1695 eq2554
    | exact resolve eq2554 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq2554
  have eq2559 : x = (k y x) := by
    first
    | (have r₁ := eq2557
       have r₂ := eq1751
       grind)
    | exact resolve eq2557 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq2557
  have eq2561 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2550
       grind)
    | exact superpose eq2550 eq24
    | exact resolve eq24 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2600 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2561
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2561
    | exact resolve eq2561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2614 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1779 eq2600
    | exact resolve eq2600 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2646 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2614 eq1780
    | exact resolve eq1780 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780 eq2614
  have eq2670 : x = (k x x) := by
    first
    | (have i₁ := eq2559
       have i₂ := eq2550
       grind)
    | exact superpose eq2550 eq2559
    | exact resolve eq2559 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550 eq2559
  have eq2672 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2670
       grind)
    | exact superpose eq2670 eq43
    | exact resolve eq43 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2670
  have eq2676 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1779 eq2672
    | exact resolve eq2672 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2677 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2676
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2676
    | exact resolve eq2676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2676
  have eq2678 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1779 eq2677
    | exact resolve eq2677 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq2677
  have eq2700 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2678 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2701 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2700
  have eq2726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2646 eq2701
    | exact resolve eq2701 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646 eq2701
  have eq2727 : False := by grind
  exact eq2727

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pyx_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  clear eq35
  have eq50 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq43
    | exact resolve eq43 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq63 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq62
       have i₂ := eq59 sF2
       grind)
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq89 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq59 sF3
       grind)
    | exact superpose eq59 eq87
    | exact resolve eq87 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq91 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq59 y
       grind)
    | exact superpose eq59 eq89
    | exact resolve eq89 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 (σ X0) (σ X1)
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq86
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq86 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq122 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq133
       have i₂ := eq59 sF1
       grind)
    | exact superpose eq59 eq133
    | exact resolve eq133 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq136
    | exact resolve eq136 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq174 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq79 (σ X0) sF2
       grind)
    | exact superpose eq79 eq39
    | (have j1 := eq79 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq268 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq59 (τ X0)
       grind)
    | exact superpose eq59 eq34
    | exact resolve eq34 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq279 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq268
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq279
    | exact resolve eq279 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq279
  have eq391 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X2 X2) ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq52 X1 X1
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq400
    | exact resolve eq400 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq406 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq397
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq397
    | exact resolve eq397 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq408 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq394
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq394
    | exact resolve eq394 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq410 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq391
    | exact resolve eq391 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq411 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq404
    | exact resolve eq404 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq415 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq410 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq410
    | exact resolve eq410 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq512 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq93 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq515 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq517 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq515
    | (have j0 := eq515 X0 X1
       grind)
    | exact resolve eq515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq554 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq64 (M.op y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq64
    | exact resolve eq64 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq575 X0
       have i₂ := eq64 (M.op X0 X0)
       grind)
    | exact superpose eq64 eq575
    | exact resolve eq575 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq588 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq554
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq554
    | exact resolve eq554 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq590 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq581
    | exact resolve eq581 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq594 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq588
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq588
    | exact resolve eq588 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq702 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq16
    | exact resolve eq16 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq406 eq52
    | exact resolve eq52 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq803 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq800
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq800
    | exact resolve eq800 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq804 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq803
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq803
    | exact resolve eq803 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq805 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq804
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq804
    | exact resolve eq804 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq806 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq805 eq399
    | exact resolve eq399 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq111 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq821 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq818
       have r₂ := eq27
       grind)
    | exact resolve eq818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq823 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq821
    | exact resolve eq821 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq825 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq408 eq52
    | exact resolve eq52 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq825
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq825
    | exact resolve eq825 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq829 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq828
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq830 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq829
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq829
    | exact resolve eq829 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq833 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq823 eq122
    | exact resolve eq122 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq823
  have eq2257 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq411 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq411
    | exact resolve eq411 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2380 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2257 X0 X1
       have i₂ := eq399 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq399 eq2257
    | exact resolve eq2257 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2513 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq52
    | exact resolve eq52 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2516 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2513 X0 X1
       have i₂ := eq52 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq2513
    | exact resolve eq2513 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq2572 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2516 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq2516
    | exact resolve eq2516 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2603 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2572 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq2572
    | exact resolve eq2572 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2616 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2603 X0 X1
       have i₂ := eq411 X1 X0
       grind)
    | exact superpose eq411 eq2603
    | exact resolve eq2603 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq2603
  have eq3853 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq174
    | (have j0 := eq174 X0
       grind)
    | exact resolve eq174 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3962 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3853 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3853
    | (have j0 := eq3853 y
       grind)
    | exact resolve eq3853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq3976 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3962
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq3962
    | exact resolve eq3962 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962
  have eq3992 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq3976
    | exact resolve eq3976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4000 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3992
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq3992
    | exact resolve eq3992 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4008 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq4000
    | exact resolve eq4000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq5330 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq7835 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq7836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7835 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq7835
    | (have j0 := eq7835 X0 X1
       grind)
    | exact resolve eq7835 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7835
  have eq7876 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7836 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7836
    | (have j0 := eq7836 X1 (τ X0)
       grind)
    | exact resolve eq7836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7836
  have eq7988 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (k X1 (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7876 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq7876
    | (have j0 := eq7876 X0 X1
       grind)
    | exact resolve eq7876 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq8009 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7988 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq7988
    | (have j0 := eq7988 X0 X1
       grind)
    | exact resolve eq7988 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7988
  have eq8023 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8009 X0 X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq8009
    | (have j0 := eq8009 X0 X1
       grind)
    | exact resolve eq8009 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq8009
  have eq8350 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X1 (M.op X0 X0) X1
       have i₂ := eq399 X1 X0
       grind)
    | exact superpose eq399 eq401
    | (have j0 := eq401 X1 (M.op X0 X0) X1
       grind)
    | exact resolve eq401 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq8453 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8350 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq8350
    | (have j0 := eq8350 X0 X1
       grind)
    | exact resolve eq8350 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350
  have eq8620 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (M.op X1 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8453 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq8453
    | (have j0 := eq8453 X0 X1
       grind)
    | exact resolve eq8453 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8453
  have eq24348 : (σ y) = (M.op (σ y) (σ (M.op y (τ (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq590 y
       have i₂ := eq833
       grind)
    | exact superpose eq833 eq590
    | exact resolve eq590 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq833
  have eq24439 : (σ y) = (M.op (σ y) (σ (M.op y (τ (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24348
    | exact resolve eq24348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24348
  have eq24597 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (τ (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24439 eq14
    | exact resolve eq14 eq24439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24616 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op y (τ (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq805 eq24597
    | exact resolve eq24597 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24597
  have eq24659 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (M.op (M.op y (τ (M.op (σ x) (σ y)))) (M.op y (τ (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24616 eq64
    | exact resolve eq64 eq24616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq24616
  have eq24727 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (M.op y (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24659
       have i₂ := eq52 (τ sF4) y
       grind)
    | exact superpose eq52 eq24659
    | exact resolve eq24659 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24659
  have eq24743 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (M.op y (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24727
       have i₂ := eq702 sF4
       grind)
    | exact superpose eq702 eq24727
    | exact resolve eq24727 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq24727
  have eq24746 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (σ (M.op y (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24743
       have i₂ := eq52 sF4 sF2
       grind)
    | exact superpose eq52 eq24743
    | exact resolve eq24743 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24743
  have eq24748 : (σ y) = (σ (M.op y (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq24746
    | exact resolve eq24746 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq24746
  have eq25152 : (σ (M.op x (M.op x y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq594
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq594
    | exact resolve eq594 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq830
  have eq25153 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq805 eq25152
    | exact resolve eq25152 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq25152
  have eq321527 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq8023 X0 X1
       have j1 := eq580 X1 X0
       grind)
    | (have r₁ := eq8023 X1 X0
       have r₂ := eq580 X0 X1
       grind)
    | exact resolve eq8023 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq8023
  have eq321624 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq24748 eq321527
    | (have j0 := eq321527 X0 y
       grind)
    | exact resolve eq321527 eq24748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24748 eq321527
  have eq616325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq111 eq321624
    | exact resolve eq321624 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq321624 eq111
    | (have j1 := eq321624 (σ x)
       grind)
    | exact resolve eq111 eq321624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq321624
  have eq616614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq616579
  have eq616647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq616325
  have eq616673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq616614
    | exact resolve eq616614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616614
  have eq616727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq616647
    | exact resolve eq616647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616647
  have eq616736 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq616673
       have r₂ := eq27
       grind)
    | exact resolve eq616673 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616673
  have eq616766 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq616727
       have r₂ := eq27
       grind)
    | exact resolve eq616727 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616727
  have eq616775 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53
       have i₂ := eq616766
       grind)
    | exact superpose eq616766 eq53
    | exact resolve eq53 eq616766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616776 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq616766
       grind)
    | exact superpose eq616766 eq91
    | exact resolve eq91 eq616766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616766
  have eq617023 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq616776
    | exact resolve eq616776 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616776
  have eq618714 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq617023 eq52
    | exact resolve eq52 eq617023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617023
  have eq618839 : (τ (σ y)) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq616736 eq108
    | exact resolve eq108 eq616736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq616736
  have eq618865 : (M.op x y) = (M.op y y) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq618839
    | exact resolve eq618839 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq618839
  have eq618873 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq616775 eq138
    | exact resolve eq138 eq616775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616775
  have eq619110 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25153 eq618873
    | exact resolve eq618873 eq25153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25153 eq618873
  have eq629508 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq619110 eq14
    | exact resolve eq14 eq619110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619110
  have eq629549 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq629508
       have i₂ := eq52 sF1 sF1
       grind)
    | exact superpose eq52 eq629508
    | exact resolve eq629508 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq629508
  have eq671925 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq629549
       have i₂ := eq2616 sF1 x
       grind)
    | (have i₁ := eq629549
       have i₂ := eq2616 sF1 sF1
       grind)
    | exact superpose eq2616 eq629549
    | exact resolve eq629549 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616 eq629549
  have eq719461 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq618714 eq671925
    | exact resolve eq671925 eq618714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618714 eq671925
  have eq719514 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq719461
  have eq779879 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k (M.op x (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq408 eq8620
    | (have j0 := eq8620 (M.op x y) x
       grind)
    | exact resolve eq8620 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq8620
  have eq779938 : y = (k y x) ∨ (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) := by
    first
    | exact superpose eq50 eq779879
    | exact resolve eq779879 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779879
  have eq780067 : (M.op y y) = (M.op x x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq779938
       have r₂ := eq618865
       grind)
    | exact resolve eq779938 eq618865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618865 eq779938
  have eq780572 : y = (M.op y (M.op y (M.op x x))) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2380 y y
       have i₂ := eq780067
       grind)
    | exact superpose eq780067 eq2380
    | exact resolve eq2380 eq780067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq780067
  have eq780604 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq780572
       have i₂ := eq399 y x
       grind)
    | exact superpose eq399 eq780572
    | exact resolve eq780572 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780572
  have eq780858 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq780604
       grind)
    | exact superpose eq780604 eq86
    | exact resolve eq86 eq780604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq780888 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq79 y x
       have i₂ := eq780604
       grind)
    | exact superpose eq780604 eq79
    | (have j0 := eq79 y x
       grind)
    | exact resolve eq79 eq780604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq780890 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5330 x y
       have i₂ := eq780604
       grind)
    | exact superpose eq780604 eq5330
    | exact resolve eq5330 eq780604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330 eq780604
  have eq780894 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq780890
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq780890
    | exact resolve eq780890 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780890
  have eq780896 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq780888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq780888
    | exact resolve eq780888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780888
  have eq780924 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq780858
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq780858
    | exact resolve eq780858 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780858
  have eq780927 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq780894
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq780894
    | exact resolve eq780894 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780894
  have eq780929 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq780896
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq780896
    | exact resolve eq780896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780896
  have eq780948 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq780927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq780927
    | exact resolve eq780927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780927
  have eq780965 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq780948
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq780948
    | exact resolve eq780948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780948
  have eq780979 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq780965
    | exact resolve eq780965 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780965
  have eq781139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4008 eq780924
    | exact resolve eq780924 eq4008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4008 eq780924
  have eq789630 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq780929
       grind)
    | exact superpose eq780929 eq91
    | exact resolve eq91 eq780929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq780929
  have eq789902 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq789630
    | exact resolve eq789630 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789630
  have eq795836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq789902 eq781139
    | exact resolve eq781139 eq789902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781139
  have eq796036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq795836
  have eq796063 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq796036
       have r₂ := eq27
       grind)
    | exact resolve eq796036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796036
  have eq797352 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq796063 eq27
    | exact resolve eq27 eq796063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797355 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq796063 eq806
    | exact resolve eq806 eq796063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq798730 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq797355
    | exact resolve eq797355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797355
  have eq807413 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq796063 eq798730
    | exact resolve eq798730 eq796063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796063 eq798730
  have eq807811 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq807413
  have eq810732 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq807811 eq789902
    | exact resolve eq789902 eq807811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789902 eq807811
  have eq810936 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq810732
  have eq810985 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq810936
       have r₂ := eq797352
       grind)
    | exact resolve eq810936 eq797352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797352 eq810936
  have eq811026 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq810985 eq20
    | exact resolve eq20 eq810985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq811028 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq810985 eq50
    | exact resolve eq50 eq810985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq810985
  have eq811701 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq811028
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq811028
    | exact resolve eq811028 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq811028
  have eq811703 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq811026
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811026
    | exact resolve eq811026 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811026
  have eq815368 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq811703 eq780979
    | exact resolve eq780979 eq811703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780979
  have eq815393 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq815368
  have eq815400 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq815393
       have r₂ := eq27
       grind)
    | exact resolve eq815393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815393
  have eq815599 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq811701 eq138
    | exact resolve eq138 eq811701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq811701
  have eq815898 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq815599
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq815599
    | exact resolve eq815599 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815599
  have eq818990 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq815898 eq815400
    | exact resolve eq815400 eq815898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815400 eq815898
  have eq819156 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by grind
  clear eq818990
  have eq819176 : x = y := by
    first
    | (have r₁ := eq819156
       have r₂ := eq811703
       grind)
    | exact resolve eq819156 eq811703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811703 eq819156
  have eq819184 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq819176
       grind)
    | exact superpose eq819176 eq18
    | exact resolve eq18 eq819176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq819185 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq819176
       grind)
    | exact superpose eq819176 eq24
    | exact resolve eq24 eq819176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq819176
  have eq819943 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq819185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq819185
    | exact resolve eq819185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819185
  have eq819984 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq819943 eq26
    | exact resolve eq26 eq819943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq821205 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq819943 eq719514
    | exact resolve eq719514 eq819943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719514 eq819943
  have eq821252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq821205
       have i₂ := eq399 sF2 sF1
       grind)
    | exact superpose eq399 eq821205
    | exact resolve eq821205 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq821205
  have eq822244 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq821252
       have r₂ := eq27
       grind)
    | exact resolve eq821252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821252
  have eq822537 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq822244 eq28
    | exact resolve eq28 eq822244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq823719 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq822537
    | exact resolve eq822537 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq822537
  have eq826218 : x = (M.op x x) := by
    first
    | exact superpose eq823719 eq819184
    | exact resolve eq819184 eq823719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819184 eq823719
  have eq826220 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq826218
       grind)
    | exact superpose eq826218 eq63
    | exact resolve eq63 eq826218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq826218
  have eq826479 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq822244 eq826220
    | exact resolve eq826220 eq822244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826220
  have eq826558 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq826479
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq826479
    | exact resolve eq826479 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq826479
  have eq826626 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq822244 eq826558
    | exact resolve eq826558 eq822244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826558
  have eq826858 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq822244 eq819984
    | exact resolve eq819984 eq822244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819984 eq822244
  have eq832982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq826626 eq826858
    | exact resolve eq826858 eq826626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826626 eq826858
  have eq832983 : False := by grind
  exact eq832983
