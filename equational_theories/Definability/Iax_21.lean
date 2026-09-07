import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4315`: `x ◇ (y ◇ x) = x ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4315 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4315 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4315.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X2)) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq8 X2 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
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
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27
    | exact resolve eq27 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq152 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X3 X2
       grind)
    | (have i₁ := eq91 X0 (M.op X1 X3)
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq91
    | (have j0 := eq91 X0 (M.op X1 X3)
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X3))
       have r₂ := eq20 X0 X0 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq91 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq20 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq305 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq311 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq20
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq319 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq33 X0 X2
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 X0 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq560 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq617 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1330 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq305
       have i₂ := eq617 y x
       grind)
    | exact superpose eq617 eq305
    | (have j1 := eq617 (σ y) (σ x)
       grind)
    | (have r₁ := eq305
       have r₂ := eq617 y x
       grind)
    | exact resolve eq305 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1331 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1330
  have eq1374 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 X1 X2
       have i₂ := eq317 X1 X0
       grind)
    | (have i₁ := eq317 X0 X1
       have i₂ := eq317 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq317 eq317
    | (have j0 := eq317 X1 X2
       have j1 := eq317 X1 X2
       grind)
    | exact resolve eq317 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
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
  have eq1419 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (k X0 X1))) = (M.op X2 (M.op (σ X0) X3)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 (σ X0) X3 (σ X1)
       have i₂ := eq317 X0 X1
       grind)
    | exact superpose eq317 eq20
    | (have j1 := eq317 X0 X1
       grind)
    | exact resolve eq20 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1431 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1381 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1381
    | (have j0 := eq1381 X0 X1
       grind)
    | exact resolve eq1381 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1381
  have eq3587 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq311 (τ X0) (τ X1) X2 X3
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq311
    | (have j0 := eq311 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq311 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (τ X0)) X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3587 X0 X1 X2 X3
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3587
    | (have j0 := eq3587 X0 X1 X2 X3
       grind)
    | exact resolve eq3587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3918 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3916 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3916
    | (have j0 := eq3916 X0 X1 X2 X3
       grind)
    | exact resolve eq3916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq3919 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3918 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3918
    | (have j0 := eq3918 X0 X1 X2 X3
       grind)
    | exact resolve eq3918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918
  have eq3920 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X1 ∨ (M.op X2 (M.op X0 X3)) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3919 X0 X1 X2 X3
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3919
    | (have j0 := eq3919 X0 X1 X2 X3
       grind)
    | exact resolve eq3919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq5595 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1431
    | (have j0 := eq1431 X1 (τ X0)
       grind)
    | exact resolve eq1431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq10596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq319
  have eq32561 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq49968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10596 (τ X1) (τ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq10596
    | exact resolve eq10596 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq49990 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10596 x x
       have i₂ := eq1331
       grind)
    | exact superpose eq1331 eq10596
    | exact resolve eq10596 eq1331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq50029 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq10596 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10596
  have eq50030 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq50029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50029
  have eq50035 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq49990
  have eq50067 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49968 X0 X1
       have i₂ := eq50030 (τ X0)
       grind)
    | exact superpose eq50030 eq49968
    | (have j0 := eq49968 X0 X1
       grind)
    | exact resolve eq49968 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49968
  have eq50084 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50067 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50067
    | (have j0 := eq50067 X0 X1
       grind)
    | exact resolve eq50067 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50067
  have eq50091 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50084 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50084
    | (have j0 := eq50084 X0 X1
       grind)
    | exact resolve eq50084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50084
  have eq50094 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50091 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50091
    | (have j0 := eq50091 X0 X1
       grind)
    | exact resolve eq50091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50091
  have eq50096 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50094 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq50094
    | (have j0 := eq50094 X0 X1
       grind)
    | exact resolve eq50094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50094
  have eq50097 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50096 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50096
    | (have j0 := eq50096 X0 X1
       grind)
    | exact resolve eq50096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq50098 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50097 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq50097
    | (have j0 := eq50097 X0 X1
       grind)
    | exact resolve eq50097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50097
  have eq50123 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50030 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50030
    | exact resolve eq50030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50217 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5595 X1 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq5595
    | (have j0 := eq5595 X1 (σ X0)
       grind)
    | exact resolve eq5595 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq50230 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = (M.op X1 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (σ X0) X2 (σ X0)
       have i₂ := eq50030 X0
       grind)
    | exact superpose eq50030 eq20
    | exact resolve eq20 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50280 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50217 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq50217
    | (have j0 := eq50217 X0 X1
       grind)
    | exact resolve eq50217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50217
  have eq50310 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq50123 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq50123
    | exact resolve eq50123 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq50123
  have eq50323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50310 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50310
    | exact resolve eq50310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50310
  have eq51544 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq50035
       grind)
    | exact superpose eq50035 eq9
    | exact resolve eq9 eq50035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50035
  have eq51636 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51544
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq51544
    | exact resolve eq51544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51544
  have eq51672 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51636
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq51636
    | exact resolve eq51636 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51636
  have eq51673 : y = (M.op x x) := by grind
  clear eq51672
  have eq51711 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 x X1 x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq20
    | exact resolve eq20 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq51755 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq32561 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq32561
    | exact resolve eq32561 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51998 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ (M.op x x) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq3920 x X2 X0 x
       have i₂ := eq51711 X0 x
       grind)
    | exact superpose eq51711 eq3920
    | (have j0 := eq3920 x X2 X2 x
       grind)
    | exact resolve eq3920 eq51711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq51711
  have eq52123 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (k x X2)) ∨ y = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq51998 X0 X2
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq51998
    | (have j0 := eq51998 X0 X2
       grind)
    | exact resolve eq51998 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51998
  have eq53161 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50230 X0 X1 X2
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq50230
    | exact resolve eq50230 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50230
  have eq53894 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53161 x X0 X1
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq53161
    | exact resolve eq53161 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161
  have eq54334 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32561 (σ x) x
       have i₂ := eq53894 (σ x) x
       grind)
    | exact superpose eq53894 eq32561
    | exact resolve eq32561 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32561
  have eq55014 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 x (M.op x y) X0 X1
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq1419
    | (have j0 := eq1419 x (M.op x y) x x
       grind)
    | exact resolve eq1419 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq55116 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq55014 X0 x
       have i₂ := eq53894 X0 x
       grind)
    | exact superpose eq53894 eq55014
    | exact resolve eq55014 eq53894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53894 eq55014
  have eq55128 : ∀ X0 : G, (M.op x y) = (τ (σ (k x x))) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55116 X0
       have i₂ := eq50030 x
       grind)
    | exact superpose eq50030 eq55116
    | (have j0 := eq55116 X0
       grind)
    | exact resolve eq55116 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50030 eq55116
  have eq55138 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55128 X0
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq55128
    | (have j0 := eq55128 X0
       grind)
    | exact resolve eq55128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55128
  have eq55144 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55138 X0
       have i₂ := eq50323 x
       grind)
    | exact superpose eq50323 eq55138
    | (have j0 := eq55138 X0
       grind)
    | exact resolve eq55138 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55138
  have eq55146 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55144 X0
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55144
    | (have j0 := eq55144 X0
       grind)
    | exact resolve eq55144 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55144
  have eq55901 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50098
  have eq55904 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55901 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55901
    | (have j0 := eq55901 X0 X1
       grind)
    | (have r₁ := eq55901 X0 X0
       have r₂ := eq50323 X0
       grind)
    | exact resolve eq55901 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55901
  have eq55993 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55904 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq55904
    | (have j0 := eq55904 X0 X1
       grind)
    | exact resolve eq55904 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55904
  have eq56345 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq55993 x x
       have i₂ := eq51673
       grind)
    | exact superpose eq51673 eq55993
    | exact resolve eq55993 eq51673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51673 eq55993
  have eq56564 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56345 (k x X0)
       have i₂ := eq52123 x X0
       grind)
    | exact superpose eq52123 eq56345
    | (have j0 := eq56345 y
       have j1 := eq52123 X0 (k x (k x X0))
       grind)
    | (have r₁ := eq56345 X0
       have r₂ := eq52123 X0 (M.op x X0)
       grind)
    | exact resolve eq56345 eq52123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52123 eq56345
  have eq58613 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq41 x (M.op (σ x) (σ y))
       have i₂ := eq54334
       grind)
    | exact superpose eq54334 eq41
    | exact resolve eq41 eq54334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54334
  have eq60805 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq50280 X0 (σ X1)
       grind)
    | exact superpose eq50280 eq9
    | (have j1 := eq50280 X0 (σ X1)
       grind)
    | exact resolve eq9 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50280
  have eq60908 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60805 X0 X1
       have i₂ := eq50323 X0
       grind)
    | exact superpose eq50323 eq60805
    | (have j0 := eq60805 X0 X1
       grind)
    | exact resolve eq60805 eq50323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50323 eq60805
  have eq60950 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60908 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq60908
    | (have j0 := eq60908 X0 X1
       grind)
    | exact resolve eq60908 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60908
  have eq62499 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq617 X2 X1
       have i₂ := eq60950 X1 X0
       grind)
    | (have i₁ := eq617 X0 X1
       have i₂ := eq60950 X0 (M.op X1 X1)
       grind)
    | exact superpose eq60950 eq617
    | (have j0 := eq617 X2 X1
       have j1 := eq60950 X1 X0
       grind)
    | exact resolve eq617 eq60950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq60950
  have eq62854 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1374 y x X0
       grind)
    | exact superpose eq1374 eq14
    | (have j1 := eq1374 y x X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1374 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq62858 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq62854 X0
       have j1 := eq62499 (σ (k x X0)) x (M.op (σ x) (σ X0))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (M.op x y)) x (σ (k x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 (σ (k x y)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq62854 X0
       have r₂ := eq62499 X0 x y
       grind)
    | exact resolve eq62854 eq62499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62499 eq62854
  have eq72325 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62858 (M.op x y)
       have i₂ := eq55146 (σ x)
       grind)
    | exact superpose eq55146 eq62858
    | (have j0 := eq62858 (M.op x y)
       grind)
    | exact resolve eq62858 eq55146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55146 eq62858
  have eq72361 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq72325
  have eq72365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72361
       have i₂ := eq51755
       grind)
    | exact superpose eq51755 eq72361
    | exact resolve eq72361 eq51755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51755 eq72361
  have eq72370 : y = (M.op x y) := by
    first
    | (have r₁ := eq72365
       have r₂ := eq14
       grind)
    | exact resolve eq72365 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72365
  have eq72389 : ∀ X0 : G, y ≠ y ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq56564 X0
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq56564
    | (have j0 := eq56564 X0
       grind)
    | (have r₁ := eq56564 X0
       have r₂ := eq72370
       grind)
    | exact resolve eq56564 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56564
  have eq72505 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq72389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72389
  have eq73386 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq72505 (τ (M.op (σ x) (σ y)))
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq72505
    | (have j0 := eq72505 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq72505 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72505
  have eq73658 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73386
       have i₂ := eq58613
       grind)
    | exact superpose eq58613 eq73386
    | exact resolve eq73386 eq58613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58613 eq73386
  have eq73659 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq73658
  have eq73822 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq73659
       grind)
    | exact superpose eq73659 eq10
    | exact resolve eq10 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73659
  have eq74390 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73822
       grind)
    | exact superpose eq73822 eq14
    | exact resolve eq14 eq73822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73822
  have eq74601 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74390
       have i₂ := eq72370
       grind)
    | exact superpose eq72370 eq74390
    | exact resolve eq74390 eq72370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72370 eq74390
  have eq74602 : False := by grind
  exact eq74602

/-- `Equation4331`: `x ◇ (y ◇ x) = z ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4331 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4331 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4331.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X1)) := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X2)) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq8 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X2 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X0 X0
       have i₂ := eq8 X0 X0 X2
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
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq142 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq37 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq37 eq13
    | (have j1 := eq37 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X1 X1) X2 X3
       have i₂ := eq17 X2 X1 X1 X0
       grind)
    | (have i₁ := eq23 X2 X2 X2
       have i₂ := eq17 X0 X1 X2 X2
       grind)
    | exact superpose eq17 eq23
    | exact resolve eq23 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq23
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq285 x X1 X3 X2
       grind)
    | (have i₁ := eq8 X0 X3 X3
       have i₂ := eq285 X0 X1 X3 X3
       grind)
    | exact superpose eq285 eq8
    | exact resolve eq8 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq35 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1104 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1104 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1971 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1163 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1163
    | (have j0 := eq1163 (τ X0) X1
       grind)
    | exact resolve eq1163 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1980 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1971
    | (have j0 := eq1971 X0 X1
       grind)
    | exact resolve eq1971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1985 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1980 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1980
    | (have j0 := eq1980 X0 X1
       grind)
    | exact resolve eq1980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2004 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1985 (τ X0) X1
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq1985
    | (have j0 := eq1985 (τ X0) X1
       grind)
    | exact resolve eq1985 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1985
  have eq2804 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2929 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2804 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2804
    | (have j0 := eq2804 X0 X1
       grind)
    | exact resolve eq2804 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq11293 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1159 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1159
    | (have j0 := eq1159 (τ X0)
       grind)
    | exact resolve eq1159 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq11319 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11293 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11293
    | (have j0 := eq11293 X0
       grind)
    | exact resolve eq11293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11293
  have eq11332 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11319 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11319
    | (have j0 := eq11319 X0
       grind)
    | exact resolve eq11319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11319
  have eq12468 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq142 x y X0
       grind)
    | exact superpose eq142 eq14
    | (have j1 := eq142 X0 y X0
       grind)
    | exact resolve eq14 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq197594 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12468 X0
       have i₂ := eq2929 x y
       grind)
    | exact superpose eq2929 eq12468
    | (have j0 := eq12468 X0
       have j1 := eq2929 X0 y
       grind)
    | (have r₁ := eq12468 X0
       have r₂ := eq2929 x y
       grind)
    | exact resolve eq12468 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929 eq12468
  have eq197596 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq197594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197594
  have eq200521 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2004 (σ y) X0
       have i₂ := eq197596 (σ y)
       grind)
    | exact superpose eq197596 eq2004
    | (have j0 := eq2004 (σ y) X0
       grind)
    | exact resolve eq2004 eq197596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq197596
  have eq200558 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq200521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200521
  have eq200574 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq200558 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq200558
    | exact resolve eq200558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200558
  have eq200585 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq200574 X0
       have j1 := eq11 X0 y
       grind)
    | (have r₁ := eq200574 X0
       have r₂ := eq11 X0 y
       grind)
    | exact resolve eq200574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200574
  have eq203868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1159 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq1159
    | (have j0 := eq1159 y
       grind)
    | exact resolve eq1159 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq203872 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11332 y
       have i₂ := eq200585 y
       grind)
    | exact superpose eq200585 eq11332
    | (have j0 := eq11332 y
       grind)
    | (have r₁ := eq11332 y
       have r₂ := eq200585 y
       grind)
    | exact resolve eq11332 eq200585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332 eq200585
  have eq203929 : y = (M.op y y) := by grind
  clear eq203872
  have eq203933 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq203868
  have eq207183 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq8
    | exact resolve eq8 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207247 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 y y
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq351
    | exact resolve eq351 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207370 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq207247 X0 X1
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207247
    | exact resolve eq207247 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207247
  have eq207381 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq207183 X0
       have i₂ := eq203929
       grind)
    | exact superpose eq203929 eq207183
    | exact resolve eq207183 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203929 eq207183
  have eq232467 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 (σ y) (σ y)
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq351
    | exact resolve eq351 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq232560 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq232467 X0 X1
       have i₂ := eq203933
       grind)
    | exact superpose eq203933 eq232467
    | exact resolve eq232467 eq203933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203933 eq232467
  have eq232697 : y = (σ y) := by
    first
    | (have i₁ := eq232560 x x
       have i₂ := eq207370 x x
       grind)
    | exact superpose eq207370 eq232560
    | exact resolve eq232560 eq207370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207370 eq232560
  have eq233940 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq232697
       grind)
    | exact superpose eq232697 eq14
    | exact resolve eq14 eq232697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233994 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq233940
       have i₂ := eq207381 (σ x)
       grind)
    | exact superpose eq207381 eq233940
    | exact resolve eq233940 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233940
  have eq234001 : y ≠ (σ y) := by
    first
    | (have i₁ := eq233994
       have i₂ := eq207381 x
       grind)
    | exact superpose eq207381 eq233994
    | exact resolve eq233994 eq207381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207381 eq233994
  have eq234002 : False := by grind
  exact eq234002

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation4385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
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
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq12 X1 (σ X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq76 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq82 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq103 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq76
    | (have j0 := eq76 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq19 X0
       grind)
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq104 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq170 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq53 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq53
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq104
    | exact resolve eq104 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X2 X0
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X2 X0
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq683 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq734 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq1569 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq82
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq82 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82
  have eq1610 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1569
    | (have j0 := eq1569 X0 X1
       grind)
    | exact resolve eq1569 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq2070 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq281 X1 X2
       have i₂ := eq281 X1 X0
       grind)
    | (have i₁ := eq281 X0 X1
       have i₂ := eq281 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq281 eq281
    | (have j0 := eq281 X1 X2
       have j1 := eq281 X1 X2
       grind)
    | exact resolve eq281 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281
    | exact resolve eq281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2089 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq2089
    | (have j0 := eq2089 X0 X1
       grind)
    | exact resolve eq2089 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq2089
  have eq2155 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2143
    | (have j0 := eq2143 X1 (τ X0)
       grind)
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2703 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1610 x y
       grind)
    | exact superpose eq1610 eq14
    | (have j1 := eq1610 x y
       grind)
    | exact resolve eq14 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : x = (k y x) := by
    first
    | (have j1 := eq734 x y
       grind)
    | (have r₁ := eq2703
       have r₂ := eq734 x y
       grind)
    | exact resolve eq2703 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2892 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq683
    | (have j0 := eq683 x y
       grind)
    | exact resolve eq683 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq283
  have eq14269 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq14611 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14269 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq14269
    | (have j0 := eq14269 X0 X1
       grind)
    | exact resolve eq14269 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq59249 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8911 (τ X1) (τ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq8911
    | exact resolve eq8911 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59661 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq8911 X0 X1
       grind)
    | exact superpose eq8911 eq9
    | (have j1 := eq8911 X0 X1
       grind)
    | exact resolve eq9 eq8911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60035 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8911 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8911
  have eq60036 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq60035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60035
  have eq60339 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59661 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq59661
    | (have j0 := eq59661 X0 X1
       grind)
    | exact resolve eq59661 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59661
  have eq60623 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq59249 X0 X1
       have i₂ := eq60036 (τ X0)
       grind)
    | exact superpose eq60036 eq59249
    | (have j0 := eq59249 X0 X1
       grind)
    | exact resolve eq59249 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59249
  have eq60862 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60339 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq60339
    | (have j0 := eq60339 X0 X1
       grind)
    | exact resolve eq60339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60339
  have eq60982 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60623 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq60623
    | (have j0 := eq60623 X0 X1
       grind)
    | exact resolve eq60623 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60623
  have eq61157 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60982 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60982
    | (have j0 := eq60982 X0 X1
       grind)
    | exact resolve eq60982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60982
  have eq61240 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61157 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61157
    | (have j0 := eq61157 X0 X1
       grind)
    | exact resolve eq61157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61157
  have eq61281 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61240
    | (have j0 := eq61240 X0 X1
       grind)
    | exact resolve eq61240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61240
  have eq61300 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61281 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq61281
    | (have j0 := eq61281 X0 X1
       grind)
    | exact resolve eq61281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61281
  have eq61305 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61300 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61300
    | (have j0 := eq61300 X0 X1
       grind)
    | exact resolve eq61300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300
  have eq61347 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60036 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60036
    | exact resolve eq60036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61427 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq61449 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61476 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X1 (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq2155
    | (have j0 := eq2155 X1 (σ X0)
       grind)
    | exact resolve eq2155 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq61494 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61556 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61476 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61476
    | (have j0 := eq61476 X0 X1
       grind)
    | exact resolve eq61476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61476
  have eq61577 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61427 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61427
    | (have j0 := eq61427 X0 X1
       grind)
    | exact resolve eq61427 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61427
  have eq61620 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq61347 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq61347
    | exact resolve eq61347 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq61347
  have eq61663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq61620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61620
    | exact resolve eq61620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61620
  have eq63339 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0
       have i₂ := eq61663 (τ X0)
       grind)
    | exact superpose eq61663 eq61
    | exact resolve eq61 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63391 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63339 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq63339
    | exact resolve eq63339 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63339
  have eq78681 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61663 X0
       have i₂ := eq61305 X0 X1
       grind)
    | (have i₁ := eq61663 X1
       have i₂ := eq61305 X1 X1
       grind)
    | exact superpose eq61305 eq61663
    | (have j1 := eq61305 X0 X1
       grind)
    | exact resolve eq61663 eq61305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78795 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78796 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61305
  have eq78797 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78796 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78796
    | (have j0 := eq78796 X0 X1
       grind)
    | (have r₁ := eq78796 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78796 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78796
  have eq78798 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78795 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78795
    | (have j0 := eq78795 X0 X1
       grind)
    | (have r₁ := eq78795 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78795 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78795
  have eq79155 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78798 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78798
    | (have j0 := eq78798 X0 X1
       grind)
    | exact resolve eq78798 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78798
  have eq87714 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61449 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61449
    | exact resolve eq61449 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61449
  have eq88129 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq61494 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61494
    | exact resolve eq61494 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61494
  have eq88916 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq61556 X1 (σ X0)
       grind)
    | exact superpose eq61556 eq13
    | (have j1 := eq61556 X1 (σ X0)
       grind)
    | exact resolve eq13 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61556
  have eq88958 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88916 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq88916
    | (have j0 := eq88916 X0 X1
       grind)
    | exact resolve eq88916 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88916
  have eq89077 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88958 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88958
    | (have j0 := eq88958 X0 X1
       grind)
    | exact resolve eq88958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88958
  have eq89277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61577 y x
       grind)
    | exact superpose eq61577 eq14
    | (have j1 := eq61577 y x
       grind)
    | exact resolve eq14 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61577
  have eq89389 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq89277
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq89277
    | exact resolve eq89277 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749 eq89277
  have eq89452 : x = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq89389
       have i₂ := eq61663 y
       grind)
    | exact superpose eq61663 eq89389
    | exact resolve eq89389 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89389
  have eq89488 : x = (M.op y y) := by
    first
    | (have r₁ := eq89452
       have r₂ := eq2892
       grind)
    | exact resolve eq89452 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq89452
  have eq89560 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq8
    | exact resolve eq8 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89566 : (M.op x y) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq53
    | exact resolve eq53 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq89584 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq230 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq230
    | exact resolve eq230 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq89725 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq79155 x y
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq79155
    | (have j0 := eq79155 x y
       grind)
    | exact resolve eq79155 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89843 : (M.op y (M.op y x)) = (M.op (M.op x y) (M.op y x)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq170 y (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq170
    | (have j0 := eq170 y (M.op y x)
       grind)
    | exact resolve eq170 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq89872 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq89843
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89843
    | exact resolve eq89843 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89843
  have eq89888 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq89872
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89872
    | exact resolve eq89872 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89872
  have eq89898 : (M.op y (M.op x y)) = (k (M.op x y) y) := by
    first
    | (have j1 := eq78797 (M.op x y) y
       grind)
    | (have r₁ := eq89888
       have r₂ := eq78797 (M.op x y) y
       grind)
    | exact resolve eq89888 eq78797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78797 eq89888
  have eq94517 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq88129 y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq88129
    | exact resolve eq88129 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88129
  have eq94695 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1610 y x
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq1610
    | (have j0 := eq1610 y x
       grind)
    | exact resolve eq1610 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq95588 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X2 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X2 X1
       have i₂ := eq89077 X0 X1
       grind)
    | (have i₁ := eq683 X0 X1
       have i₂ := eq89077 (M.op X1 X1) X1
       grind)
    | exact superpose eq89077 eq683
    | (have j0 := eq683 X2 X1
       have j1 := eq89077 X0 X1
       grind)
    | exact resolve eq683 eq89077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89077
  have eq97472 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = X0 ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq2070 x y X0
       grind)
    | exact superpose eq2070 eq14
    | (have j1 := eq2070 x y X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq97478 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq97472 X0
       have j1 := eq95588 (σ (k y X0)) x (M.op (σ X0) (σ y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (k y x)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 X0 y x
       grind)
    | exact resolve eq97472 eq95588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95588 eq97472
  have eq97575 : ∀ X0 : G, (M.op (σ (k y X0)) (σ y)) = (M.op (σ y) (σ (M.op y y))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq87714 y (σ X0)
       have i₂ := eq97478 X0
       grind)
    | exact superpose eq97478 eq87714
    | (have j1 := eq97478 X0
       grind)
    | exact resolve eq87714 eq97478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87714 eq97478
  have eq97656 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97575 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq97575
    | (have j0 := eq97575 X0
       grind)
    | exact resolve eq97575 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97575
  have eq97710 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97656 X0
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq97656
    | (have j0 := eq97656 X0
       grind)
    | exact resolve eq97656 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94517 eq97656
  have eq100781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq94695
       grind)
    | exact superpose eq94695 eq14
    | exact resolve eq14 eq94695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94695
  have eq100886 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq100781
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq100781 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100898 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq734 y x
       grind)
    | exact superpose eq734 eq100781
    | (have j1 := eq734 y x
       grind)
    | exact resolve eq100781 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq100781
  have eq100904 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) := by grind
  clear eq100898
  have eq100910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100904
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100904
    | exact resolve eq100904 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100904
  have eq100911 : y = (k x y) := by grind
  clear eq100910
  have eq100930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100886
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100886
    | exact resolve eq100886 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100886
  have eq100931 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq100930
  have eq100941 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100931
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100931
    | exact resolve eq100931 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100931
  have eq100992 : (τ y) = (τ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14611 y x
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq14611
    | (have j0 := eq14611 y x
       grind)
    | exact resolve eq14611 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14611
  have eq101008 : (τ y) = (τ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100992
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100992
    | exact resolve eq100992 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100992
  have eq101124 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq100941
       grind)
    | exact superpose eq100941 eq8
    | exact resolve eq8 eq100941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100941
  have eq101168 : x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101124
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101124
    | exact resolve eq101124 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101124
  have eq101186 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101168
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq101168
    | exact resolve eq101168 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101168
  have eq101410 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89725
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq89725
    | exact resolve eq89725 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89725
  have eq101467 : y = (M.op x x) ∨ x ≠ (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101410
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq101410
    | exact resolve eq101410 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101410
  have eq101468 : x ≠ (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq101467
  have eq101765 : (σ (M.op (τ y) (τ y))) = (k (M.op x y) (σ (M.op (τ y) (τ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21 (M.op x y)
       have i₂ := eq101008
       grind)
    | exact superpose eq101008 eq21
    | exact resolve eq21 eq101008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101008
  have eq101805 : (σ (τ (M.op y y))) = (k (M.op x y) (σ (τ (M.op y y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101765
       have i₂ := eq63391 y
       grind)
    | exact superpose eq63391 eq101765
    | exact resolve eq101765 eq63391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63391 eq101765
  have eq101815 : (M.op y y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101805
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq101805
    | exact resolve eq101805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101805
  have eq101818 : x = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101815
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101815
    | exact resolve eq101815 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101815
  have eq103037 : x = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101818
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq101818
    | exact resolve eq101818 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101186 eq101818
  have eq103049 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq103037
  have eq103054 : x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103049
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq103049
    | exact resolve eq103049 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103049
  have eq103055 : y = (M.op x x) := by
    first
    | (have r₁ := eq103054
       have r₂ := eq101468
       grind)
    | exact resolve eq103054 eq101468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101468 eq103054
  have eq112125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq97710 X0
       have i₂ := eq683 X0 y
       grind)
    | exact superpose eq683 eq97710
    | (have j0 := eq97710 X0
       have j1 := eq683 X0 y
       grind)
    | exact resolve eq97710 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq97710
  have eq112221 : ∀ X0 : G, x = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq112125 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq112125
    | (have j0 := eq112125 X0
       grind)
    | exact resolve eq112125 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112125
  have eq112222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq112221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112221
  have eq119914 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60862 X0 X1
       have i₂ := eq78681 X0 X1
       grind)
    | exact superpose eq78681 eq60862
    | (have j1 := eq78681 X1 X0
       grind)
    | exact resolve eq60862 eq78681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60862 eq78681
  have eq120099 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq119914 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq119914
    | (have j0 := eq119914 X0 X1
       grind)
    | exact resolve eq119914 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119914
  have eq120145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120099 X0 X1
       have j1 := eq79155 X1 X0
       grind)
    | (have r₁ := eq120099 X1 X0
       have r₂ := eq79155 X0 X1
       grind)
    | (have r₁ := eq120099 X0 X0
       have r₂ := eq79155 X0 X0
       grind)
    | exact resolve eq120099 eq79155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79155 eq120099
  have eq127955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op X0 y) y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq112222 X0
       have i₂ := eq120145 (M.op X0 y) y
       grind)
    | exact superpose eq120145 eq112222
    | (have j0 := eq112222 X0
       have j1 := eq120145 (M.op X0 y) y
       grind)
    | exact resolve eq112222 eq120145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112222 eq120145
  have eq128140 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq127955 X0
       have i₂ := eq8 y X0
       grind)
    | exact superpose eq8 eq127955
    | (have j0 := eq127955 X0
       grind)
    | exact resolve eq127955 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127955
  have eq128192 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128140 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128140
    | (have j0 := eq128140 X0
       grind)
    | exact resolve eq128140 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128140
  have eq128212 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128192 X0
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128192
    | (have j0 := eq128192 X0
       grind)
    | exact resolve eq128192 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128192
  have eq128220 : ∀ X0 : G, x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq128212 X0
       grind)
    | (have r₁ := eq128212 X0
       have r₂ := eq14
       grind)
    | exact resolve eq128212 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128212
  have eq128222 : ∀ X0 : G, x = (k y (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq128220 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128220
    | (have j0 := eq128220 (k y (M.op X0 y))
       grind)
    | exact resolve eq128220 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128220
  have eq128239 : x = (k y (M.op y (M.op y y))) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128222 (M.op y (M.op y y))
       have i₂ := eq19 y
       grind)
    | exact superpose eq19 eq128222
    | (have j0 := eq128222 (k y (M.op y (M.op y y)))
       grind)
    | exact resolve eq128222 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq128279 : x = (k y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128222 (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq128222
    | (have j0 := eq128222 x
       grind)
    | exact resolve eq128222 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89566 eq128222
  have eq128487 : x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128279
       have i₂ := eq89584
       grind)
    | exact superpose eq89584 eq128279
    | exact resolve eq128279 eq89584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89584 eq128279
  have eq128515 : x = (M.op y (M.op y y)) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128239
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq128239
    | exact resolve eq128239 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq128239
  have eq128516 : x = (M.op y (M.op y y)) := by grind
  clear eq128515
  have eq128611 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128487
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128487
    | exact resolve eq128487 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89560 eq128487
  have eq128612 : x = (M.op x y) := by grind
  clear eq128611
  have eq128641 : x = (M.op y x) := by
    first
    | (have i₁ := eq128516
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128516
    | exact resolve eq128516 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89488 eq128516
  have eq128779 : (M.op y x) = (k x y) := by
    first
    | (have i₁ := eq89898
       have i₂ := eq128612
       grind)
    | exact superpose eq128612 eq89898
    | exact resolve eq89898 eq128612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89898 eq128612
  have eq128963 : y = (M.op y x) := by
    first
    | (have i₁ := eq128779
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq128779
    | exact resolve eq128779 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100911 eq128779
  have eq129005 : x = y := by
    first
    | (have i₁ := eq128963
       have i₂ := eq128641
       grind)
    | exact superpose eq128641 eq128963
    | exact resolve eq128963 eq128641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128641 eq128963
  have eq129053 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129005
       grind)
    | exact superpose eq129005 eq14
    | exact resolve eq14 eq129005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129005
  have eq129287 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq129053
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129053
    | exact resolve eq129053 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129053
  have eq129312 : (σ y) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq129287
       have i₂ := eq60036 x
       grind)
    | exact superpose eq60036 eq129287
    | exact resolve eq129287 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60036 eq129287
  have eq129321 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq129312
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq129312
    | exact resolve eq129312 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61663 eq129312
  have eq129325 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq129321
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129321
    | exact resolve eq129321 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103055 eq129321
  have eq129326 : False := by grind
  exact eq129326

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4386 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4386 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq135 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X1 X1) X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq77
    | (have j0 := eq77 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq77 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)
       have r₂ := eq8 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq77 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X2 ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 (k X1 X1)
       have j1 := eq28 X2 X1 X2
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X2) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq8
    | (have j1 := eq28 (M.op (M.op X0 X1) X0) X1 X2
       grind)
    | exact resolve eq8 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq298 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq325 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq335 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq123
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq123 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq352 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq1125 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1125
    | (have j0 := eq1125 X0 X1
       grind)
    | exact resolve eq1125 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1475 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2335 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq71 X0 X0
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2775 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X1 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq325
    | (have j0 := eq325 X1 X0
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq325 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq325
  have eq2826 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2775 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2775
    | (have j0 := eq2775 X0 X1
       grind)
    | exact resolve eq2775 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq7029 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X0
       have i₂ := eq184 X1 X0 X0
       grind)
    | exact superpose eq184 eq135
    | (have j0 := eq135 X0 X0
       have j1 := eq184 X0 X0 x
       grind)
    | exact resolve eq135 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq7123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7029 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7029
  have eq11751 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq14
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq14 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11859 : y = (k y x) := by
    first
    | (have j1 := eq1475 x y
       grind)
    | (have r₁ := eq11751
       have r₂ := eq1475 x y
       grind)
    | exact resolve eq11751 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq12166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq183 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq12167 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq12265 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1223 x y
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq1223
    | (have j0 := eq1223 x y
       grind)
    | exact resolve eq1223 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13658 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq14586 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq184 X2 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq184
    | (have j0 := eq184 X0 X0 X2
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq184 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq14707 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq14586 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14586
  have eq58255 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq149 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq149
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq149 X0 X0
       have r₂ := eq12 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq149 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq70258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2826 x y
       grind)
    | exact superpose eq2826 eq14
    | (have j1 := eq2826 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq70265 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq70258
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq70258
    | exact resolve eq70258 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70258
  have eq70532 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70265
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq70265
    | (have r₁ := eq70265
       have r₂ := eq12265
       grind)
    | exact resolve eq70265 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70265
  have eq70533 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq70532
  have eq70588 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq70533
       grind)
    | exact superpose eq70533 eq9
    | exact resolve eq9 eq70533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70533
  have eq70599 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70588
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70588
    | exact resolve eq70588 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70588
  have eq70700 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29 y y
       have i₂ := eq70599
       grind)
    | exact superpose eq70599 eq29
    | exact resolve eq29 eq70599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70599
  have eq70730 : x = (M.op y y) ∨ x = y := by grind
  clear eq70700
  have eq70967 : x = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq7123 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq7123
    | exact resolve eq7123 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq70973 : y = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq14707 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq14707
    | exact resolve eq14707 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14707
  have eq75777 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13658 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13658
    | exact resolve eq13658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13658
  have eq75783 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75777 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75777
    | (have j0 := eq75777 X0 X1
       grind)
    | exact resolve eq75777 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75777
  have eq75784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75783 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75783
    | (have j0 := eq75783 X0 X1
       grind)
    | exact resolve eq75783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75783
  have eq75785 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op (M.op X1 X0) X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75784 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75784
    | (have j0 := eq75784 X0 X1
       grind)
    | exact resolve eq75784 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75784
  have eq75786 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75785 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75785
    | (have j0 := eq75785 X0 X1
       grind)
    | exact resolve eq75785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75785
  have eq76154 : x = y ∨ x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq70967
       have i₂ := eq70973
       grind)
    | exact superpose eq70973 eq70967
    | exact resolve eq70967 eq70973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70967 eq70973
  have eq76171 : x = (k y y) ∨ x = y := by grind
  clear eq76154
  have eq77724 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq77725 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77724 X0 X1
       have j1 := eq298 X1 X0
       grind)
    | (have r₁ := eq77724 (k X1 X1) X0
       have r₂ := eq298 X0 X1
       grind)
    | (have r₁ := eq77724 X0 (σ (k X1 X1))
       have r₂ := eq298 (σ X0) X1
       grind)
    | (have r₁ := eq77724 X1 X0
       have r₂ := eq298 X0 X1
       grind)
    | exact resolve eq77724 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq77724
  have eq77763 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq77725 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq77725 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq77725 eq16
    | (have j1 := eq77725 (τ X1) X0
       grind)
    | exact resolve eq16 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq77764 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq77725 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq77725 X0 (σ X0)
       grind)
    | exact superpose eq77725 eq9
    | (have j1 := eq77725 X1 X0
       grind)
    | exact resolve eq9 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77725
  have eq77788 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77763 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq77763
    | (have j0 := eq77763 X0 X1
       grind)
    | exact resolve eq77763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77763
  have eq77794 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77788 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77788
    | (have j0 := eq77788 X0 X1
       grind)
    | exact resolve eq77788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77788
  have eq78535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq77764 (σ X0) X1
       grind)
    | exact superpose eq77764 eq13
    | (have j1 := eq77764 (σ X0) X1
       grind)
    | exact resolve eq13 eq77764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77764
  have eq78543 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78535 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78535
    | (have j0 := eq78535 X0 X1
       grind)
    | exact resolve eq78535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78535
  have eq79380 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq78543 x y
       grind)
    | exact superpose eq78543 eq14
    | (have j1 := eq78543 x y
       grind)
    | exact resolve eq14 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79400 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq79380
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq79380
    | exact resolve eq79380 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859 eq79380
  have eq79428 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79400
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq79400
    | (have r₁ := eq79400
       have r₂ := eq12265
       grind)
    | exact resolve eq79400 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265 eq79400
  have eq79429 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq79428
  have eq79534 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79429
  have eq79572 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq79534
  have eq80107 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq79572
  have eq80130 : x = (M.op y y) := by
    first
    | (have r₁ := eq80107
       have r₂ := eq70730
       grind)
    | exact resolve eq80107 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70730 eq80107
  have eq80301 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq8
    | exact resolve eq8 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80311 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq61
    | exact resolve eq61 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq80469 : x ≠ y ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq58255 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq58255
    | (have j0 := eq58255 y y
       grind)
    | exact resolve eq58255 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58255
  have eq80477 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq80469
       have r₂ := eq76171
       grind)
    | exact resolve eq80469 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80469
  have eq82213 : x ≠ y ∨ x = (k y y) := by grind
  clear eq80477
  have eq82243 : x = (k y y) := by
    first
    | (have r₁ := eq82213
       have r₂ := eq76171
       grind)
    | exact resolve eq82213 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76171 eq82213
  have eq82388 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq77794 X0 y
       have i₂ := eq82243
       grind)
    | exact superpose eq82243 eq77794
    | (have j0 := eq77794 X0 y
       grind)
    | exact resolve eq77794 eq82243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82243
  have eq82589 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq82388 (τ X0)
       grind)
    | exact superpose eq82388 eq17
    | (have j1 := eq82388 (τ X0)
       grind)
    | exact resolve eq17 eq82388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq82388
  have eq97164 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq82589 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82589
    | exact resolve eq82589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82589
  have eq97185 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97164 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq97164
    | (have j0 := eq97164 X0
       grind)
    | exact resolve eq97164 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97164
  have eq104969 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq75786 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq75786
    | (have j0 := eq75786 X0 x
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq75786 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167 eq75786
  have eq105001 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104969
  have eq105019 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105001 X0
       have j1 := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 X0
       have r₂ := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 (k x x)
       have r₂ := eq77794 (k (k x x) (k x x)) x
       grind)
    | exact resolve eq105001 eq77794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77794 eq105001
  have eq105252 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq105019 (σ X0)
       grind)
    | exact superpose eq105019 eq13
    | exact resolve eq13 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105252 X0
       have i₂ := eq105019 X0
       grind)
    | exact superpose eq105019 eq105252
    | exact resolve eq105252 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105252
  have eq105850 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq8
    | exact resolve eq8 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105898 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0) (σ X0)
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq18
    | exact resolve eq18 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108231 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq105850 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105850
    | exact resolve eq105850 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105850
  have eq108520 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq108231 (σ X0)
       have i₂ := eq78543 X0 y
       grind)
    | exact superpose eq78543 eq108231
    | (have j1 := eq78543 X0 y
       grind)
    | exact resolve eq108231 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108910 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108520 X0
       have i₂ := eq105019 y
       grind)
    | exact superpose eq105019 eq108520
    | (have j0 := eq108520 X0
       grind)
    | exact resolve eq108520 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108520
  have eq109023 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq108910 X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq108910
    | (have j0 := eq108910 X0
       grind)
    | exact resolve eq108910 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108910
  have eq109176 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq105898 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105898
    | exact resolve eq105898 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80130 eq105898
  have eq109626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq108231 x
       have i₂ := eq109176 x
       grind)
    | exact superpose eq109176 eq108231
    | exact resolve eq108231 eq109176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108231 eq109176
  have eq110255 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq352 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq352
    | (have j0 := eq352 y x
       grind)
    | exact resolve eq352 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq110260 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq78543 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq78543
    | (have j0 := eq78543 y x
       grind)
    | exact resolve eq78543 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78543
  have eq110320 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110260
       have i₂ := eq105019 x
       grind)
    | exact superpose eq105019 eq110260
    | exact resolve eq110260 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105019 eq110260
  have eq113771 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110255
       grind)
    | exact superpose eq110255 eq14
    | exact resolve eq14 eq110255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110255
  have eq113824 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113771
       have i₂ := eq1475 y x
       grind)
    | exact superpose eq1475 eq113771
    | (have j1 := eq1475 y x
       grind)
    | exact resolve eq113771 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq113771
  have eq113826 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) := by grind
  clear eq113824
  have eq113827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113826
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113826
    | exact resolve eq113826 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113826
  have eq113828 : x = (k x y) := by grind
  clear eq113827
  have eq113872 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1223 y x
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq1223
    | (have j0 := eq1223 y x
       grind)
    | exact resolve eq1223 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq113906 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113872
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113872
    | exact resolve eq113872 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80301 eq113872
  have eq116340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110320
       grind)
    | exact superpose eq110320 eq14
    | exact resolve eq14 eq110320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110320
  have eq116369 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116340
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq116340
    | exact resolve eq116340 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113828 eq116340
  have eq116377 : y = (M.op x x) := by
    first
    | (have r₁ := eq116369
       have r₂ := eq113906
       grind)
    | exact resolve eq116369 eq113906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113906 eq116369
  have eq116419 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116543 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq118947 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq80311 X0
       have i₂ := eq116419 X0
       grind)
    | exact superpose eq116419 eq80311
    | exact resolve eq80311 eq116419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116419
  have eq131575 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq109023 X0
       have i₂ := eq97185 X0
       grind)
    | exact superpose eq97185 eq109023
    | (have j0 := eq109023 X0
       have j1 := eq97185 X0
       grind)
    | exact resolve eq109023 eq97185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97185 eq109023
  have eq131582 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq131575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131575
  have eq131591 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq131582 X0
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq131582
    | (have j0 := eq131582 X0
       grind)
    | exact resolve eq131582 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109626 eq131582
  have eq136182 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131591 (M.op x y)
       have i₂ := eq116543
       grind)
    | exact superpose eq116543 eq131591
    | (have j0 := eq131591 (M.op x y)
       grind)
    | exact resolve eq131591 eq116543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116543 eq131591
  have eq136198 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136182
       have i₂ := eq105332 (M.op x y)
       grind)
    | exact superpose eq105332 eq136182
    | exact resolve eq136182 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136182
  have eq136199 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136198
       have i₂ := eq80311 x
       grind)
    | exact superpose eq80311 eq136198
    | exact resolve eq136198 eq80311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80311 eq136198
  have eq136200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136199
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136199
    | exact resolve eq136199 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136199
  have eq136201 : x = (M.op x y) := by
    first
    | (have r₁ := eq136200
       have r₂ := eq14
       grind)
    | exact resolve eq136200 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136200
  have eq136352 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq118947 x
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq118947
    | exact resolve eq118947 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118947
  have eq136686 : y = (M.op x y) := by
    first
    | (have i₁ := eq136352
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136352
    | exact resolve eq136352 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116377 eq136352
  have eq136848 : x = y := by
    first
    | (have i₁ := eq136686
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq136686
    | exact resolve eq136686 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136201 eq136686
  have eq137233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136848
       grind)
    | exact superpose eq136848 eq14
    | exact resolve eq14 eq136848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136848
  have eq137712 : False := by grind
  exact eq137712

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
