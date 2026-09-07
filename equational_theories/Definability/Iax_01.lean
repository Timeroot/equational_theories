import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation508 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law508 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (τ X1)
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (M.op X0 X0)
       have i₂ := eq73 X0 (σ X1)
       grind)
    | exact superpose eq73 eq88
    | exact resolve eq88 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq164 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 (σ X0) X1
       grind)
    | (have i₁ := eq37 X0 X0
       have i₂ := eq24 X0 (σ X0)
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq179 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq14
    | (have j1 := eq37 x y
       grind)
    | exact resolve eq14 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq361 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (τ X1)
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq420 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 (τ (M.op X0 X0))
       have i₂ := eq141 X0 (σ X1)
       grind)
    | exact superpose eq141 eq88
    | exact resolve eq88 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq141
  have eq1017 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (M.op X0 X0))
       have i₂ := eq97 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq97 eq164
    | (have j0 := eq164 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq164 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1018 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq361 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq361 eq164
    | (have j0 := eq164 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq420 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq420 eq164
    | (have j0 := eq164 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq164 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq420
  have eq1076 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1078 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq1018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1079 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1017 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1102 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq1076
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2374 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq179
       have i₂ := eq31 y X0 x
       grind)
    | exact superpose eq31 eq179
    | (have j1 := eq31 y X0 x
       grind)
    | exact resolve eq179 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq179
  have eq2382 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq2374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq13563 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ y)) ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 (σ x) X0
       have i₂ := eq2382 X1
       grind)
    | exact superpose eq2382 eq1102
    | (have j1 := eq2382 X1
       grind)
    | exact resolve eq1102 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq13621 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13563 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13563
    | (have j0 := eq13563 X0 X1
       grind)
    | exact resolve eq13563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13563
  have eq14214 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq13621 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq14215 : y = (M.op y y) := by grind
  clear eq14214
  have eq14431 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq19
    | exact resolve eq19 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14443 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1078 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1078
    | exact resolve eq1078 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq14444 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1079 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1079
    | exact resolve eq1079 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq14445 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq1102 y X0
       have i₂ := eq14215
       grind)
    | exact superpose eq14215 eq1102
    | exact resolve eq1102 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq14215
  have eq14480 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq14444 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14444
    | exact resolve eq14444 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14444
  have eq14481 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq14443 x
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq14443
    | exact resolve eq14443 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14443 eq14445
  have eq14485 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq14481
       have i₂ := eq14480
       grind)
    | exact superpose eq14480 eq14481
    | exact resolve eq14481 eq14480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480 eq14481
  have eq14486 : y = (τ y) := by
    first
    | (have i₁ := eq14485
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14485
    | exact resolve eq14485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14485
  have eq14783 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14486
       grind)
    | exact superpose eq14486 eq10
    | exact resolve eq10 eq14486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14486
  have eq15721 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14783
       grind)
    | exact superpose eq14783 eq14
    | exact resolve eq14 eq14783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq15805 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq15721
       have i₂ := eq14431 (σ x)
       grind)
    | exact superpose eq14431 eq15721
    | exact resolve eq15721 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15721
  have eq15834 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15805
       have i₂ := eq14431 x
       grind)
    | exact superpose eq14431 eq15805
    | exact resolve eq15805 eq14431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431 eq15805
  have eq15835 : False := by grind
  exact eq15835

/-- `Equation543`: `x = y ◇ (z ◇ (x ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation543 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law543 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X1 X2)))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 X2))) (M.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X1 (M.op X2 (M.op X0 (M.op X1 X2)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X2 X1))
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 X0))) = X2 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq17
  have eq46 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 (M.op X0 X2)) X1
       have i₂ := eq19 X1 X2 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X2 X1))) = X2 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 X1 X0 X2
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 x X0 X1 X1
       have i₂ := eq46 x X1 (M.op X0 X1)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46
  have eq214 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq30
  have eq279 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq182 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq182 eq8
    | exact resolve eq8 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X1 X1)
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq182
    | exact resolve eq182 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq705 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (σ X1)
       grind)
    | exact superpose eq463 eq38
    | exact resolve eq38 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq706 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq463 X0 (τ X1)
       grind)
    | exact superpose eq463 eq16
    | exact resolve eq16 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq13223 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 X0 X0 X0
       have i₂ := eq341 X0 X1
       grind)
    | (have i₁ := eq117 X0 X1 X1
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq117
    | exact resolve eq117 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq13556 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq13223 X0 x X2
       have i₂ := eq182 x (M.op X0 X0)
       grind)
    | exact superpose eq182 eq13223
    | (have j0 := eq13223 X0 x X2
       grind)
    | exact resolve eq13223 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223
  have eq14658 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq341 X1 X2
       have i₂ := eq13556 X2 X0
       grind)
    | exact superpose eq13556 eq341
    | (have j1 := eq13556 X1 X0
       grind)
    | exact resolve eq341 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14770 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X1 (σ (M.op X1 X1))
       have i₂ := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq706
    | (have j1 := eq13556 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq706 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq14772 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq705 X1 (τ (M.op X1 X1))
       have i₂ := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq13556 eq705
    | (have j1 := eq13556 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq705 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq14782 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14785 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14772
  have eq14786 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14770
  have eq15298 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X1 X1
       have i₂ := eq14785 X1 X0
       grind)
    | exact superpose eq14785 eq182
    | exact resolve eq182 eq14785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq15722 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq14785 x X2
       have i₂ := eq14786 x X0
       grind)
    | exact superpose eq14786 eq14785
    | exact resolve eq14785 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14785 eq14786
  have eq16318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq214
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq214
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq16319 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq16318
  have eq38175 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14782 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq14782
    | (have j0 := eq14782 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq14782 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq14782 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38191 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38175 X0 X1
       have j1 := eq14782 X1 X0
       grind)
    | (have r₁ := eq38175 X1 X1
       have r₂ := eq14782 X1 X1
       grind)
    | (have r₁ := eq38175 (M.op X0 X0) X1
       have r₂ := eq14782 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq38175 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq14782 X0 (M.op X1 X1)
       grind)
    | exact resolve eq38175 eq14782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14782 eq38175
  have eq38311 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X1 X0
       grind)
    | (have i₁ := eq38191 X1 X2
       have i₂ := eq341 X0 X1
       grind)
    | exact superpose eq341 eq38191
    | (have j0 := eq38191 X1 X2
       grind)
    | (have r₁ := eq38191 (M.op X1 X1) X1
       have r₂ := eq341 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq38191 (M.op X0 X0) X1
       have r₂ := eq341 X0 (M.op X0 X0)
       grind)
    | exact resolve eq38191 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq38191
  have eq91292 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (k X0 X0) = (M.op X3 X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq463 X2 x
       have i₂ := eq14658 X0 x X2
       grind)
    | (have i₁ := eq463 X0 x
       have i₂ := eq14658 (M.op X0 X0) x X2
       grind)
    | exact superpose eq14658 eq463
    | (have j1 := eq14658 X0 X3 X2
       grind)
    | exact resolve eq463 eq14658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq14658
  have eq95390 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91292 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91292
  have eq95397 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq95390 X0 X1
       have j1 := eq13556 X1 X0
       grind)
    | (have r₁ := eq95390 (k x x) X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 x X0
       have r₂ := eq13556 X0 x
       grind)
    | (have r₁ := eq95390 (M.op X0 X0) X1
       have r₂ := eq13556 X0 (M.op X1 X1)
       grind)
    | exact resolve eq95390 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556 eq95390
  have eq96228 : ∀ X0 X2 : G, (σ (k X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15722 x X2
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq15722
    | exact resolve eq15722 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq96269 : ∀ X0 X2 X3 : G, (k X0 X0) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq38311 x X2 X3
       have i₂ := eq95397 X0 x
       grind)
    | exact superpose eq95397 eq38311
    | (have j0 := eq38311 X0 X2 X3
       grind)
    | (have r₁ := eq38311 x (k X0 X0) X2
       have r₂ := eq95397 X0 x
       grind)
    | exact resolve eq38311 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38311
  have eq96384 : ∀ X0 X1 : G, (k X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15298 X1 (τ (M.op X1 X1))
       have i₂ := eq95397 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq95397 eq15298
    | exact resolve eq15298 eq95397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298 eq95397
  have eq110561 : ∀ X0 : G, (k X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 (σ x)
       have i₂ := eq16319
       grind)
    | exact superpose eq16319 eq96384
    | exact resolve eq96384 eq16319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16319
  have eq110597 : ∀ X0 : G, y = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq110561 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq110561
    | exact resolve eq110561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110561
  have eq110627 : y = (M.op x x) := by
    first
    | (have j1 := eq96269 x y x
       grind)
    | (have r₁ := eq110597 x
       have r₂ := eq96269 x y x
       grind)
    | exact resolve eq110597 eq96269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96269 eq110597
  have eq110642 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq279 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq279
    | exact resolve eq279 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq110695 : ∀ X0 : G, (σ (k X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96228 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96228
    | exact resolve eq96228 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96228
  have eq110697 : ∀ X0 : G, (k X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq96384 X0 x
       have i₂ := eq110627
       grind)
    | exact superpose eq110627 eq96384
    | exact resolve eq96384 eq110627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96384 eq110627
  have eq110828 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq110695 x
       have i₂ := eq110697 x
       grind)
    | exact superpose eq110697 eq110695
    | exact resolve eq110695 eq110697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110695 eq110697
  have eq110880 : y = (τ y) := by
    first
    | (have i₁ := eq110828
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq110828
    | exact resolve eq110828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110828
  have eq111068 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq110880
       grind)
    | exact superpose eq110880 eq10
    | exact resolve eq10 eq110880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110880
  have eq111159 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq111068
       grind)
    | exact superpose eq111068 eq14
    | exact resolve eq14 eq111068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111068
  have eq111193 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq111159
       have i₂ := eq110642 (σ x)
       grind)
    | exact superpose eq110642 eq111159
    | exact resolve eq111159 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111159
  have eq111205 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq111193
       have i₂ := eq110642 x
       grind)
    | exact superpose eq110642 eq111193
    | exact resolve eq111193 eq110642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110642 eq111193
  have eq111206 : False := by grind
  exact eq111206

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation646 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq120 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq116 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq116 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq120 (σ X1) (σ X0)
       grind)
    | exact superpose eq120 eq13
    | exact resolve eq13 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq120 X1 X0
       grind)
    | exact superpose eq120 eq144
    | exact resolve eq144 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq144
  have eq1499 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq14
    | (have r₁ := eq14
       have r₂ := eq149 x y
       grind)
    | exact resolve eq14 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1519 : False := by grind
  exact eq1519

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyy_pxy_Equation655 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq8 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2) X0 X1
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
  clear eq16
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op (M.op X2 X1) X2))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) = (M.op (M.op X1 (M.op (M.op X2 X1) X2)) (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X2)) = (k X0 (M.op X1 (M.op (M.op X2 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1 X2
       have i₂ := eq8 (M.op X1 (M.op (M.op X2 X1) X2)) X1 X2
       grind)
    | exact superpose eq8 eq32
    | exact resolve eq32 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 x x (M.op X0 X0) X1
       have i₂ := eq21 X0 (M.op X0 X0) x x
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq125 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq97 X1 (M.op X1 X1)
       grind)
    | exact superpose eq97 eq133
    | exact resolve eq133 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq152 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op (M.op X1 X0) X1))) = (k X2 (σ (M.op X0 (M.op (M.op X1 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq33 (τ X2) X0 X1
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq33
  have eq164 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq137 (σ X1) X0
       grind)
    | exact superpose eq137 eq28
    | exact resolve eq28 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq137
  have eq173 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq622 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq182
    | (have j0 := eq182 (τ X0) (τ X1)
       grind)
    | exact resolve eq182 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq182
  have eq629 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq633 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq636 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq637 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq636
    | (have j0 := eq636 X0 X1
       grind)
    | exact resolve eq636 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq173
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq173 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq746
  have eq754 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq747
       grind)
    | exact superpose eq747 eq8
    | exact resolve eq8 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq756 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq97 (σ x) (σ y)
       grind)
    | exact superpose eq97 eq754
    | exact resolve eq754 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq796 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq164 (σ y) x
       have i₂ := eq756 (σ y)
       grind)
    | exact superpose eq756 eq164
    | exact resolve eq164 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq756
  have eq825 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq796 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq796
    | exact resolve eq796 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1008 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq637 X0 y
       have i₂ := eq825 X0
       grind)
    | exact superpose eq825 eq637
    | (have j0 := eq637 X0 y
       grind)
    | (have r₁ := eq637 y y
       have r₂ := eq825 y
       grind)
    | exact resolve eq637 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq2859 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1008 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq3256 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq97 y X0
       have i₂ := eq2859
       grind)
    | exact superpose eq2859 eq97
    | exact resolve eq97 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq3923 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq3256 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3924 : x = (M.op x y) := by grind
  clear eq3923
  have eq4504 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq8
    | exact resolve eq8 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4518 : ∀ X0 : G, (σ (M.op y (M.op x x))) = (k X0 (σ (M.op y (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq152 y x x
       have i₂ := eq3924
       grind)
    | exact superpose eq3924 eq152
    | exact resolve eq152 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3924
  have eq4520 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4518 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4518
    | exact resolve eq4518 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518
  have eq4533 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4504 X0
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq4504
    | exact resolve eq4504 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq5581 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq637 X0 (σ y)
       have i₂ := eq4520 X0
       grind)
    | exact superpose eq4520 eq637
    | (have j0 := eq637 X0 (σ y)
       grind)
    | (have r₁ := eq637 (σ y) (σ y)
       have r₂ := eq4520 (σ y)
       grind)
    | exact resolve eq637 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq4520
  have eq7369 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq5581 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq7439 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 (σ y) X0
       have i₂ := eq7369
       grind)
    | exact superpose eq7369 eq97
    | exact resolve eq97 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq7369
  have eq7698 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq7439 (σ x)
       grind)
    | exact superpose eq7439 eq14
    | exact resolve eq14 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7702 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7698
       have i₂ := eq4533 x
       grind)
    | exact superpose eq4533 eq7698
    | exact resolve eq7698 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq7698
  have eq7703 : False := by grind
  exact eq7703

/-- `Equation658`: `x = x ◇ (y ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation658 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law658 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law658.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X0 X0) (M.op X1 X1)) X1
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1) X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq50 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) x
       have i₂ := eq23 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq8
    | exact resolve eq8 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq91 X0 (τ X1)
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq432 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1077 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq1142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1194 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X1 X1
       have i₂ := eq1142 X0 X1
       grind)
    | exact superpose eq1142 eq118
    | (have j1 := eq1142 X2 X0
       grind)
    | exact resolve eq118 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1142
  have eq2216 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (M.op X0 X0)
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq432
    | (have j0 := eq432 (M.op X0 X0)
       grind)
    | exact resolve eq432 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq2231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq432 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq432
    | (have j0 := eq432 (τ X0)
       grind)
    | exact resolve eq432 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq432
  have eq2245 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2231
    | (have j0 := eq2231 X0
       grind)
    | exact resolve eq2231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2260 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2251
    | (have j0 := eq2251 X0
       grind)
    | exact resolve eq2251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2732 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ (M.op X0 X0)) X1
       have i₂ := eq2245 X0
       grind)
    | exact superpose eq2245 eq72
    | exact resolve eq72 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq3039 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq103 x y X0
       grind)
    | exact superpose eq103 eq14
    | (have j1 := eq103 X0 y X0
       grind)
    | exact resolve eq14 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3121 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq3039 X0
       have j1 := eq1194 y X0 x
       grind)
    | (have r₁ := eq3039 X0
       have r₂ := eq1194 y x x
       grind)
    | exact resolve eq3039 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq3039
  have eq3169 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ y)
       have i₂ := eq3121 (σ X0)
       grind)
    | exact superpose eq3121 eq29
    | exact resolve eq29 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3121
  have eq3175 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3169 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3169
    | exact resolve eq3169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3307 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2260 y
       have i₂ := eq3175 y
       grind)
    | exact superpose eq3175 eq2260
    | (have j0 := eq2260 y
       grind)
    | (have r₁ := eq2260 y
       have r₂ := eq3175 y
       grind)
    | exact resolve eq2260 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq3175
  have eq3327 : y = (M.op y y) := by grind
  clear eq3307
  have eq3443 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq72
    | exact resolve eq72 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3457 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2732 y X0
       have i₂ := eq3327
       grind)
    | exact superpose eq3327 eq2732
    | exact resolve eq2732 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq3327
  have eq4016 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3457 (σ x)
       grind)
    | exact superpose eq3457 eq14
    | exact resolve eq14 eq3457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq4024 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4016
       have i₂ := eq3443 x
       grind)
    | exact superpose eq3443 eq4016
    | exact resolve eq4016 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443 eq4016
  have eq4025 : False := by grind
  exact eq4025

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation695 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law695 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq8 (M.op X0 X0) X2 X1
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  clear eq17
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq19 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) (M.op (M.op X1 X1) X0) X2
       have i₂ := eq19 (M.op (M.op X2 X2) (M.op (M.op X1 X1) X0)) X1 X0
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X1 (M.op X1 X1)
       have i₂ := eq44 (M.op X1 X1) X0 x
       grind)
    | (have i₁ := eq19 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq44 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq44 eq19
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq44
  have eq286 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq300 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq378 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 (M.op (M.op X2 X2) X1) X0
       grind)
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq235 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq235 eq8
    | exact resolve eq8 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X0
       have i₂ := eq235 X0 (σ X0)
       grind)
    | exact superpose eq235 eq31
    | exact resolve eq31 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq235
  have eq471 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (σ X1)
       grind)
    | exact superpose eq378 eq39
    | exact resolve eq39 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq378 X0 (τ X1)
       grind)
    | exact superpose eq378 eq16
    | exact resolve eq16 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq553 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 X3 x (M.op X0 (M.op X2 X2))
       have i₂ := eq51 X2 x X0
       grind)
    | exact superpose eq51 eq19
    | exact resolve eq19 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51
  have eq2449 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (k X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ (M.op X0 X0))
       have i₂ := eq471 X0 (σ X1)
       grind)
    | exact superpose eq471 eq39
    | exact resolve eq39 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq471
  have eq2725 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (τ X1)
       grind)
    | exact superpose eq472 eq16
    | exact resolve eq16 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3641 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq3793 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3641 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq3641
    | (have j0 := eq3641 X0 X1
       grind)
    | exact resolve eq3641 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq5945 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (M.op X0 X0))
       have i₂ := eq472 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq472 eq392
    | (have j0 := eq392 X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq392 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq5946 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq2725 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq2725 eq392
    | (have j0 := eq392 X1 (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq5948 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq2449 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq2449 eq392
    | (have j0 := eq392 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq392 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq5949 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (M.op X0 X0)
       have i₂ := eq247 X0 X0
       grind)
    | exact superpose eq247 eq392
    | (have j0 := eq392 X1 (M.op X0 X0)
       grind)
    | exact resolve eq392 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq392
  have eq6107 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq6108 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq6110 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq5946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946
  have eq6111 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5945 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq6147 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6108 X0 X1
       have i₂ := eq10 (τ (M.op X0 X0))
       grind)
    | exact superpose eq10 eq6108
    | exact resolve eq6108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6346 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6107 X0 x
       grind)
    | exact superpose eq6107 eq6107
    | exact resolve eq6107 eq6107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6727 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6147 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6766 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6147
    | exact resolve eq6147 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6854 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6147 X0 x
       grind)
    | exact superpose eq6147 eq6107
    | exact resolve eq6107 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6865 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op (M.op X2 X2) X1) X1 X2
       have i₂ := eq6147 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6900 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X1
       have i₂ := eq6147 X0 (M.op X1 X1)
       grind)
    | exact superpose eq6147 eq8
    | exact resolve eq8 eq6147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7355 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq286
       have i₂ := eq3793 y x
       grind)
    | exact superpose eq3793 eq286
    | (have j1 := eq3793 (σ y) (σ x)
       grind)
    | (have r₁ := eq286
       have r₂ := eq3793 y x
       grind)
    | exact resolve eq286 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq3793
  have eq7356 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq7355
  have eq7427 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6346 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6346
    | exact resolve eq6346 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6346
  have eq8365 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (τ (τ (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq6766 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6766
    | exact resolve eq6766 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8502 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq6107 X2 x
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6107
    | exact resolve eq6107 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8505 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6147 x X1
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6147
    | exact resolve eq6147 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8510 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq6727 x X2
       have i₂ := eq6766 X0 x
       grind)
    | exact superpose eq6766 eq6727
    | exact resolve eq6727 eq6766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727 eq6766
  have eq8877 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6854 X1 x
       have i₂ := eq6111 X0 x
       grind)
    | exact superpose eq6111 eq6854
    | exact resolve eq6854 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq88511 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6147 (σ x) X0
       have i₂ := eq7356
       grind)
    | exact superpose eq7356 eq6147
    | exact resolve eq6147 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq88682 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq88511 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq88511
    | exact resolve eq88511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88511
  have eq90596 : y ≠ y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq88682 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88682
  have eq90597 : y = (M.op x x) := by grind
  clear eq90596
  have eq91165 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq53
    | exact resolve eq53 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq91201 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq386 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq386
    | exact resolve eq386 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq91207 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1 x
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq553
    | exact resolve eq553 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq91215 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6107 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6107
    | exact resolve eq6107 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6107
  have eq91216 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6110 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6110
    | exact resolve eq6110 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq91217 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6111 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6111
    | exact resolve eq6111 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq91218 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq6147 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6147
    | exact resolve eq6147 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq91272 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq6865 x X1 X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq6865
    | exact resolve eq6865 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq91297 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7427 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq7427
    | exact resolve eq7427 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq91300 : ∀ X0 : G, (τ (τ (M.op X0 X0))) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8365 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8365
    | exact resolve eq8365 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365
  have eq91302 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8502 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8502
    | exact resolve eq8502 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8502
  have eq91304 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8505 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8505
    | exact resolve eq8505 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq91305 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8510 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8510
    | exact resolve eq8510 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq91308 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq8877 x X0
       have i₂ := eq90597
       grind)
    | exact superpose eq90597 eq8877
    | exact resolve eq8877 eq90597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8877 eq90597
  have eq91332 : (σ (σ (σ y))) = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq91305 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91305
    | exact resolve eq91305 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91305
  have eq91333 : (τ (τ y)) = (τ (σ (σ (σ y)))) := by
    first
    | (have i₁ := eq91300 x
       have i₂ := eq91308 x
       grind)
    | exact superpose eq91308 eq91300
    | exact resolve eq91300 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91300
  have eq91335 : (σ (σ (σ y))) = (τ (τ y)) := by
    first
    | (have i₁ := eq91297 x
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq91297
    | exact resolve eq91297 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91297
  have eq91380 : (σ (σ y)) = (τ y) := by
    first
    | (have i₁ := eq91217 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91217
    | exact resolve eq91217 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91217
  have eq91381 : (σ (σ (σ y))) = (τ y) := by
    first
    | (have i₁ := eq91216 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91216
    | exact resolve eq91216 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91216
  have eq91385 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq91207 X0 x
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91207
    | exact resolve eq91207 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91207
  have eq91387 : ∀ X1 : G, (M.op X1 y) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq91201 x X1
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq91201
    | exact resolve eq91201 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91201
  have eq91413 : ∀ X1 : G, (M.op y (M.op X1 (τ y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq91165 x X1
       have i₂ := eq91272 x X1
       grind)
    | exact superpose eq91272 eq91165
    | exact resolve eq91165 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91165
  have eq91427 : (σ (σ y)) = (τ (τ y)) := by
    first
    | (have i₁ := eq91333
       have i₂ := eq9 (σ (σ y))
       grind)
    | exact superpose eq9 eq91333
    | exact resolve eq91333 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91333
  have eq91453 : (τ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq91381
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91381
    | exact resolve eq91381 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91381
  have eq91478 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq91413 X1
       have i₂ := eq91385 X1
       grind)
    | exact superpose eq91385 eq91413
    | exact resolve eq91413 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91413
  have eq91488 : (τ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq91427
       have i₂ := eq91380
       grind)
    | exact superpose eq91380 eq91427
    | exact resolve eq91427 eq91380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91380 eq91427
  have eq91502 : y = (τ y) := by
    first
    | (have i₁ := eq91453
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq91453
    | exact resolve eq91453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91453
  have eq92197 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq10
    | exact resolve eq10 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92198 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq16
    | exact resolve eq16 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq92790 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq14
    | exact resolve eq14 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92812 : ∀ X0 : G, (τ (M.op y y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 y x
       have i₂ := eq92197
       grind)
    | exact superpose eq92197 eq300
    | exact resolve eq300 eq92197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq92813 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92812 X0
       have i₂ := eq91308 y
       grind)
    | exact superpose eq91308 eq92812
    | (have j0 := eq92812 X0
       grind)
    | exact resolve eq92812 eq91308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91308 eq92812
  have eq92824 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92813 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq92813
    | (have j0 := eq92813 X0
       grind)
    | exact resolve eq92813 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92813
  have eq92835 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92824 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq92824
    | (have j0 := eq92824 X0
       grind)
    | exact resolve eq92824 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92824
  have eq92839 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq92835 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq92835
    | (have j0 := eq92835 X0
       grind)
    | exact resolve eq92835 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92835
  have eq96559 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (τ (σ y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6900 x X0 X1
       have i₂ := eq91215 x
       grind)
    | exact superpose eq91215 eq6900
    | exact resolve eq6900 eq91215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900 eq91215
  have eq96990 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) (τ y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq96559 x X1
       have i₂ := eq91272 x (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91272 eq96559
    | exact resolve eq96559 eq91272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91272 eq96559
  have eq97367 : ∀ X1 : G, (M.op (M.op X1 (τ (σ y))) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq96990 X1
       have i₂ := eq91385 (M.op X1 (τ (σ y)))
       grind)
    | exact superpose eq91385 eq96990
    | exact resolve eq96990 eq91385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91385 eq96990
  have eq97677 : ∀ X1 : G, (M.op (M.op X1 y) y) = X1 := by
    intro X1
    first
    | (have i₁ := eq97367 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq97367
    | exact resolve eq97367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97367
  have eq109143 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq91478 (M.op X0 y)
       have i₂ := eq97677 X0
       grind)
    | exact superpose eq97677 eq91478
    | exact resolve eq91478 eq97677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91478 eq97677
  have eq120277 : ∀ X0 : G, (σ (M.op X0 y)) = (k y (σ X0)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq91387 X0
       grind)
    | exact superpose eq91387 eq32
    | (have j0 := eq32 y X0
       grind)
    | exact resolve eq32 eq91387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq91387
  have eq120856 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op (τ y) (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120277 X0
       have i₂ := eq92198 X0
       grind)
    | exact superpose eq92198 eq120277
    | (have j0 := eq120277 X0
       grind)
    | exact resolve eq120277 eq92198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92198 eq120277
  have eq121161 : ∀ X0 : G, (τ (τ (τ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq120856 X0
       have i₂ := eq91304 (τ y)
       grind)
    | exact superpose eq91304 eq120856
    | (have j0 := eq120856 X0
       grind)
    | exact resolve eq120856 eq91304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91304 eq120856
  have eq121297 : ∀ X0 : G, (σ (σ (σ y))) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121161 X0
       have i₂ := eq91332
       grind)
    | exact superpose eq91332 eq121161
    | (have j0 := eq121161 X0
       grind)
    | exact resolve eq121161 eq91332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91332 eq121161
  have eq121402 : ∀ X0 : G, (τ (τ y)) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121297 X0
       have i₂ := eq91335
       grind)
    | exact superpose eq91335 eq121297
    | (have j0 := eq121297 X0
       grind)
    | exact resolve eq121297 eq91335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91335 eq121297
  have eq121469 : ∀ X0 : G, (τ y) = X0 ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq121402 X0
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq121402
    | (have j0 := eq121402 X0
       grind)
    | exact resolve eq121402 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121402
  have eq121527 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121469 X0
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq121469
    | (have j0 := eq121469 X0
       grind)
    | exact resolve eq121469 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121469
  have eq295331 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq121527 X0
       have i₂ := eq92839 X0
       grind)
    | exact superpose eq92839 eq121527
    | (have j0 := eq121527 X0
       have j1 := eq92839 X0
       grind)
    | exact resolve eq121527 eq92839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92839 eq121527
  have eq295341 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq295331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295331
  have eq301791 : (M.op (σ x) y) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92790
       have i₂ := eq295341 x
       grind)
    | exact superpose eq295341 eq92790
    | (have j1 := eq295341 x
       grind)
    | exact resolve eq92790 eq295341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295341
  have eq301797 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq301791
       have i₂ := eq109143 (σ x)
       grind)
    | exact superpose eq109143 eq301791
    | (have r₁ := eq301791
       have r₂ := eq109143 (σ x)
       grind)
    | exact resolve eq301791 eq109143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301791
  have eq301798 : x = y := by grind
  clear eq301797
  have eq301971 : x = (σ x) := by
    first
    | (have i₁ := eq92197
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92197
    | exact resolve eq92197 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92197
  have eq301975 : (σ (M.op x x)) ≠ (M.op (σ x) x) := by
    first
    | (have i₁ := eq92790
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq92790
    | exact resolve eq92790 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92790
  have eq301985 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq109143 X0
       have i₂ := eq301798
       grind)
    | exact superpose eq301798 eq109143
    | exact resolve eq109143 eq301798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109143 eq301798
  have eq302096 : (σ (M.op x x)) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq301975
       have i₂ := eq301985 (σ x)
       grind)
    | exact superpose eq301985 eq301975
    | exact resolve eq301975 eq301985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301975 eq301985
  have eq302197 : (M.op x x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq302096
       have i₂ := eq301971
       grind)
    | exact superpose eq301971 eq302096
    | exact resolve eq302096 eq301971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301971 eq302096
  have eq302267 : (M.op x x) ≠ (τ (τ y)) := by
    first
    | (have i₁ := eq302197
       have i₂ := eq91302 x
       grind)
    | exact superpose eq91302 eq302197
    | exact resolve eq302197 eq91302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91302 eq302197
  have eq302310 : (M.op x x) ≠ (τ y) := by
    first
    | (have i₁ := eq302267
       have i₂ := eq91488
       grind)
    | exact superpose eq91488 eq302267
    | exact resolve eq302267 eq91488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91488 eq302267
  have eq302337 : y ≠ (M.op x x) := by
    first
    | (have i₁ := eq302310
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302310
    | exact resolve eq302310 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302310
  have eq302357 : y ≠ (τ y) := by
    first
    | (have i₁ := eq302337
       have i₂ := eq91218 x
       grind)
    | exact superpose eq91218 eq302337
    | exact resolve eq302337 eq91218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91218 eq302337
  have eq302367 : y ≠ y := by
    first
    | (have i₁ := eq302357
       have i₂ := eq91502
       grind)
    | exact superpose eq91502 eq302357
    | (have r₁ := eq302357
       have r₂ := eq91502
       grind)
    | exact resolve eq302357 eq91502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91502 eq302357
  have eq302368 : False := by grind
  exact eq302368

/-- `Equation844`: `x = x ◇ ((y ◇ y) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation844 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law844 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law844.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 (M.op (M.op X0 X0) x)
       have i₂ := eq8 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq46 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 X0
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq46 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq46 eq13
    | (have j1 := eq46 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq66 X0 (τ X1)
       grind)
    | exact superpose eq66 eq15
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq205 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq734 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1205 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X1 X1
       have i₂ := eq790 X0 X1
       grind)
    | exact superpose eq790 eq101
    | (have j1 := eq790 X2 X0
       grind)
    | exact resolve eq101 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq790
  have eq1248 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (M.op X0 X0)
       have i₂ := eq66 X0 (M.op X0 X0)
       grind)
    | exact superpose eq66 eq205
    | (have j0 := eq205 (M.op X0 X0)
       grind)
    | exact resolve eq205 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1261 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq205 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq205
    | (have j0 := eq205 (τ X0)
       grind)
    | exact resolve eq205 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq205
  have eq1272 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1276 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1261 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1261
    | (have j0 := eq1261 X0
       grind)
    | exact resolve eq1261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1276 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1276
    | (have j0 := eq1276 X0
       grind)
    | exact resolve eq1276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1661 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ (M.op X0 X0)) X1
       have i₂ := eq1272 X0
       grind)
    | exact superpose eq1272 eq60
    | exact resolve eq60 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1723 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq89 x y X0
       grind)
    | exact superpose eq89 eq14
    | (have j1 := eq89 X0 y X0
       grind)
    | exact resolve eq14 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1785 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1723 X0
       have j1 := eq1205 y X0 x
       grind)
    | (have r₁ := eq1723 X0
       have r₂ := eq1205 y x x
       grind)
    | exact resolve eq1723 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1723
  have eq1825 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ y)
       have i₂ := eq1785 (σ X0)
       grind)
    | exact superpose eq1785 eq33
    | exact resolve eq33 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1785
  have eq1831 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1825 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1825
    | exact resolve eq1825 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1952 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y
       have i₂ := eq1831 y
       grind)
    | exact superpose eq1831 eq1285
    | (have j0 := eq1285 y
       grind)
    | (have r₁ := eq1285 y
       have r₂ := eq1831 y
       grind)
    | exact resolve eq1285 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq1831
  have eq1970 : y = (M.op y y) := by grind
  clear eq1952
  have eq2064 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq60
    | exact resolve eq60 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq2812 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1661 y X0
       have i₂ := eq1970
       grind)
    | exact superpose eq1970 eq1661
    | exact resolve eq1661 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1970
  have eq3010 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2812 (σ x)
       grind)
    | exact superpose eq2812 eq14
    | exact resolve eq14 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2812
  have eq3025 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3010
       have i₂ := eq2064 x
       grind)
    | exact superpose eq2064 eq3010
    | exact resolve eq3010 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064 eq3010
  have eq3026 : False := by grind
  exact eq3026

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation887 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X0 X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X1
       have i₂ := eq19 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq21 (M.op X1 X1) X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X0) X1
       have i₂ := eq23 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq297 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq370 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 (M.op X1 X1) X0
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq104
    | (have j0 := eq104 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq104 (M.op X0 X0) X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq104 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq104
  have eq372 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq403 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq419 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq19
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq492 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq372 (σ X0) X1
       grind)
    | exact superpose eq372 eq46
    | exact resolve eq46 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq493 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq372 (τ X0) X1
       grind)
    | exact superpose eq372 eq17
    | exact resolve eq17 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq494 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq495 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq492
    | exact resolve eq492 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1170 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq446 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq446
    | (have j0 := eq446 (τ X0)
       grind)
    | exact resolve eq446 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq446
  have eq1180 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1170 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1170
    | (have j0 := eq1170 X0
       grind)
    | exact resolve eq1170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1185 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1180 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1180
    | (have j0 := eq1180 X0
       grind)
    | exact resolve eq1180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq2364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq403
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq403
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq2375 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2364
  have eq3120 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq419 (τ X0) (τ X1)
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq419
    | (have j0 := eq419 (τ X0) (τ X1)
       grind)
    | exact resolve eq419 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq419
  have eq3311 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3120 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3120
    | (have j0 := eq3120 X0 X1
       grind)
    | exact resolve eq3120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3338 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3311 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3311
    | (have j0 := eq3311 X0 X1
       grind)
    | exact resolve eq3311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3344 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3338
    | (have j0 := eq3338 X0 X1
       grind)
    | exact resolve eq3338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3349 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3344
    | (have j0 := eq3344 X0 X1
       grind)
    | exact resolve eq3344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3350 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3349 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3349
    | (have j0 := eq3349 X0 X1
       grind)
    | exact resolve eq3349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3713 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 X2
       have i₂ := eq3350 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq3350 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3350 eq23
    | (have j1 := eq3350 X2 X0
       grind)
    | exact resolve eq23 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (M.op X0 (k X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 X1
       grind)
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3350 eq91
    | (have j1 := eq3350 X1 X0
       grind)
    | exact resolve eq91 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3350
  have eq4679 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3713 X1 X2 X0
       grind)
    | exact superpose eq3713 eq19
    | (have j1 := eq3713 X1 X2 X2
       grind)
    | exact resolve eq19 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq5729 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3723 X1 X0 X2
       grind)
    | exact superpose eq3723 eq19
    | (have j1 := eq3723 X1 X1 X2
       grind)
    | exact resolve eq19 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3723
  have eq7684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4679 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq7685 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7684 X0
       have j1 := eq5729 X0 X0 x
       grind)
    | (have r₁ := eq7684 x
       have r₂ := eq5729 X0 x x
       grind)
    | exact resolve eq7684 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729 eq7684
  have eq8009 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq7685 X0
       grind)
    | exact superpose eq7685 eq21
    | exact resolve eq21 eq7685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685
  have eq8848 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X0 X0) X1 X2
       have i₂ := eq8009 X0
       grind)
    | exact superpose eq8009 eq18
    | exact resolve eq18 eq8009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8895 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8848 X0 X1 x
       have i₂ := eq24 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq24 eq8848
    | exact resolve eq8848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8848
  have eq9771 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X1
       have i₂ := eq8895 X1 X0
       grind)
    | exact superpose eq8895 eq1185
    | (have j0 := eq1185 X1
       grind)
    | (have r₁ := eq1185 (M.op X1 X1)
       have r₂ := eq8895 (M.op X1 X1) X1
       grind)
    | exact resolve eq1185 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq9825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 (σ (M.op X1 X1)) X1
       have i₂ := eq8895 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq494
    | exact resolve eq494 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq9832 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 (τ (M.op X1 X1)) X1
       have i₂ := eq8895 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq495
    | exact resolve eq495 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq12480 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9832 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9832
    | exact resolve eq9832 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12577 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9825 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9825
    | exact resolve eq9825 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq12582 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X1
       have i₂ := eq9832 X1 X0
       grind)
    | exact superpose eq9832 eq21
    | exact resolve eq21 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq18918 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12582 (τ (M.op X0 X0)) X1
       have i₂ := eq12582 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq12582 eq12582
    | exact resolve eq12582 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12582
  have eq27584 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq495 X0 (σ x)
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq495
    | exact resolve eq495 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq2375
  have eq27665 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq27584 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27584
    | exact resolve eq27584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27584
  have eq32502 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8009 y
       have i₂ := eq27665 y
       grind)
    | exact superpose eq27665 eq8009
    | exact resolve eq8009 eq27665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009 eq27665
  have eq32571 : y = (M.op y y) := by
    first
    | (have j1 := eq9771 x y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 y y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 x y
       grind)
    | exact resolve eq32502 eq9771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq32502
  have eq32588 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq23
    | exact resolve eq23 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq32592 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq39 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq39
    | exact resolve eq39 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq32613 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq9832 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq9832
    | exact resolve eq9832 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9832
  have eq32624 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq12480 y X0
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq12480
    | exact resolve eq12480 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12480 eq32571
  have eq33072 : ∀ X0 : G, y = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18918 X0 y
       have i₂ := eq32588 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq32588 eq18918
    | exact resolve eq18918 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18918
  have eq33077 : y = (τ (τ y)) := by
    first
    | (have i₁ := eq33072 x
       have i₂ := eq32624 x
       grind)
    | exact superpose eq32624 eq33072
    | exact resolve eq33072 eq32624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624 eq33072
  have eq33937 : ∀ X0 : G, (σ y) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12577 X0 x
       have i₂ := eq32592 x
       grind)
    | exact superpose eq32592 eq12577
    | exact resolve eq12577 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577 eq32592
  have eq34116 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq33937 x
       have i₂ := eq32613 x
       grind)
    | exact superpose eq32613 eq33937
    | exact resolve eq33937 eq32613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32613 eq33937
  have eq34172 : y = (σ y) := by
    first
    | (have i₁ := eq34116
       have i₂ := eq33077
       grind)
    | exact superpose eq33077 eq34116
    | exact resolve eq34116 eq33077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33077 eq34116
  have eq34709 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34172
       grind)
    | exact superpose eq34172 eq14
    | exact resolve eq14 eq34172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34172
  have eq34816 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq34709
       have i₂ := eq32588 (σ x)
       grind)
    | exact superpose eq32588 eq34709
    | exact resolve eq34709 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34709
  have eq34845 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34816
       have i₂ := eq32588 x
       grind)
    | exact superpose eq32588 eq34816
    | exact resolve eq34816 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32588 eq34816
  have eq34846 : False := by grind
  exact eq34846
