import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation313 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law313 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X0) X1
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq142 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq51
  have eq159 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq142 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq142
    | exact resolve eq142 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq171 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq447 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ (k X0 X1)) (M.op (σ X0) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq18
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq6428 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq491 (M.op X0 X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq491
    | (have j0 := eq491 (M.op X0 X0)
       grind)
    | exact resolve eq491 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6434 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq6428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq14542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq33 y x
       grind)
    | exact superpose eq33 eq447
    | (have j1 := eq33 y x
       grind)
    | exact resolve eq447 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq108 y x
       grind)
    | exact superpose eq108 eq447
    | (have j1 := eq108 y x
       grind)
    | exact resolve eq447 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq14550 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq14543
  have eq14551 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14542
  have eq14588 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq131 (σ x)
       have i₂ := eq14550
       grind)
    | exact superpose eq14550 eq131
    | exact resolve eq131 eq14550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq14550
  have eq14688 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14588
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq14588
    | exact resolve eq14588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14588
  have eq16939 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq14688
       grind)
    | exact superpose eq14688 eq9
    | exact resolve eq9 eq14688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14688
  have eq16984 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16939
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq16939
    | exact resolve eq16939 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16939
  have eq16985 : y = (k y y) := by
    first
    | (have j1 := eq171 y y
       grind)
    | (have r₁ := eq16984
       have r₂ := eq171 y y
       grind)
    | exact resolve eq16984 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq491 y
       have i₂ := eq16985
       grind)
    | exact superpose eq16985 eq491
    | (have j0 := eq491 y
       grind)
    | exact resolve eq491 eq16985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq17486 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq108 y y
       have i₂ := eq16985
       grind)
    | exact superpose eq16985 eq108
    | (have j0 := eq108 y x
       grind)
    | exact resolve eq108 eq16985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq16985
  have eq17488 : y = (M.op y y) := by grind
  clear eq17486
  have eq17492 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17478
  have eq17710 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq117 y x
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq117
    | exact resolve eq117 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq19158 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op y (σ (M.op X0 X0))) y) := by
    intro X0
    first
    | (have i₁ := eq6434 X0
       have i₂ := eq17710 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17710 eq6434
    | exact resolve eq6434 eq17710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434
  have eq46401 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq47010 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op y (σ (M.op X0 X0))) y) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46401 X0
       have i₂ := eq17710 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17710 eq46401
    | (have j0 := eq46401 X0
       grind)
    | exact resolve eq46401 eq17710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17710 eq46401
  have eq47188 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47010 X0
       have i₂ := eq19158 X0
       grind)
    | exact superpose eq19158 eq47010
    | (have j0 := eq47010 X0
       grind)
    | exact resolve eq47010 eq19158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19158 eq47010
  have eq47279 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47188 X0
       have i₂ := eq8 (σ X0) (σ X0)
       grind)
    | exact superpose eq8 eq47188
    | (have j0 := eq47188 X0
       grind)
    | exact resolve eq47188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47188
  have eq47280 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq47279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47279
  have eq47584 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq47280 X0
       grind)
    | exact superpose eq47280 eq8
    | exact resolve eq8 eq47280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83496 : x = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq159 x
       have i₂ := eq14551
       grind)
    | exact superpose eq14551 eq159
    | exact resolve eq159 eq14551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq14551
  have eq83725 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83496
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83496
    | exact resolve eq83496 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83496
  have eq83779 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq83725
       grind)
    | exact superpose eq83725 eq33
    | (have j0 := eq33 y x
       grind)
    | exact resolve eq33 eq83725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq83725
  have eq83791 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq83779
  have eq84289 : x = (k x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19 y x
       have i₂ := eq83791
       grind)
    | exact superpose eq83791 eq19
    | exact resolve eq19 eq83791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq83791
  have eq84384 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84289
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq84289
    | exact resolve eq84289 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488 eq84289
  have eq84407 : x = (k x y) := by
    first
    | (have j1 := eq171 x y
       grind)
    | (have r₁ := eq84384
       have r₂ := eq171 x y
       grind)
    | exact resolve eq84384 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq84384
  have eq85343 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq84407
       grind)
    | exact superpose eq84407 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq84407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq84407
  have eq85352 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85343
       have i₂ := eq17492
       grind)
    | exact superpose eq17492 eq85343
    | exact resolve eq85343 eq17492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492 eq85343
  have eq85358 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85352
       have i₂ := eq8 (σ x) (σ x)
       grind)
    | exact superpose eq8 eq85352
    | exact resolve eq85352 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85352
  have eq85359 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq85358
  have eq85363 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85359
       have i₂ := eq47280 x
       grind)
    | exact superpose eq47280 eq85359
    | exact resolve eq85359 eq47280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47280 eq85359
  have eq85744 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq85363
       grind)
    | exact superpose eq85363 eq9
    | exact resolve eq9 eq85363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85923 : y = (M.op x x) := by
    first
    | (have i₁ := eq85744
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq85744
    | exact resolve eq85744 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85744
  have eq86436 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq85923
       grind)
    | exact superpose eq85923 eq8
    | exact resolve eq8 eq85923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85923
  have eq116337 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47584 x
       have i₂ := eq85363
       grind)
    | exact superpose eq85363 eq47584
    | exact resolve eq47584 eq85363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47584 eq85363
  have eq116756 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq116337
       grind)
    | exact superpose eq116337 eq14
    | exact resolve eq14 eq116337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116337
  have eq116950 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq116756
       have i₂ := eq86436
       grind)
    | exact superpose eq86436 eq116756
    | exact resolve eq116756 eq86436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86436 eq116756
  have eq116951 : False := by grind
  exact eq116951

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation313 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law313 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X0)) X1) = X1 := by
    intro X0 X1
    grind
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq57 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq40
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X0) X1
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq171 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq453 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X1)) (M.op (σ X1) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X1) (σ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq18
    | (have j1 := eq35 X1 X0
       grind)
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq497 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq6437 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq497 (M.op X0 X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq497
    | (have j0 := eq497 (M.op X0 X0)
       grind)
    | exact resolve eq497 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6443 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq6437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6437
  have eq14559 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq453
       have i₂ := eq33 y x
       grind)
    | exact superpose eq33 eq453
    | (have j1 := eq33 y x
       grind)
    | exact resolve eq453 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq453
       have i₂ := eq109 y x
       grind)
    | exact superpose eq109 eq453
    | (have j1 := eq109 y x
       grind)
    | exact resolve eq453 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq14567 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq14560
  have eq14568 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14559
  have eq14604 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq131 (σ x)
       have i₂ := eq14567
       grind)
    | exact superpose eq14567 eq131
    | exact resolve eq131 eq14567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq14567
  have eq14705 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14604
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq14604
    | exact resolve eq14604 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq16955 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq14705
       grind)
    | exact superpose eq14705 eq9
    | exact resolve eq9 eq14705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14705
  have eq17000 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16955
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq16955
    | exact resolve eq16955 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16955
  have eq17001 : y = (k y y) := by
    first
    | (have j1 := eq171 y y
       grind)
    | (have r₁ := eq17000
       have r₂ := eq171 y y
       grind)
    | exact resolve eq17000 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17000
  have eq17494 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq497 y
       have i₂ := eq17001
       grind)
    | exact superpose eq17001 eq497
    | (have j0 := eq497 y
       grind)
    | exact resolve eq497 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq17502 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq109 y y
       have i₂ := eq17001
       grind)
    | exact superpose eq17001 eq109
    | (have j0 := eq109 y x
       grind)
    | exact resolve eq109 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq17001
  have eq17504 : y = (M.op y y) := by grind
  clear eq17502
  have eq17508 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17494
  have eq17726 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq118 y x
       have i₂ := eq17504
       grind)
    | exact superpose eq17504 eq118
    | exact resolve eq118 eq17504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq19174 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op y (σ (M.op X0 X0))) y) := by
    intro X0
    first
    | (have i₁ := eq6443 X0
       have i₂ := eq17726 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17726 eq6443
    | exact resolve eq6443 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443
  have eq46540 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq47148 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op y (σ (M.op X0 X0))) y) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46540 X0
       have i₂ := eq17726 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17726 eq46540
    | (have j0 := eq46540 X0
       grind)
    | exact resolve eq46540 eq17726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17726 eq46540
  have eq47326 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47148 X0
       have i₂ := eq19174 X0
       grind)
    | exact superpose eq19174 eq47148
    | (have j0 := eq47148 X0
       grind)
    | exact resolve eq47148 eq19174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19174 eq47148
  have eq47417 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47326 X0
       have i₂ := eq8 (σ X0) (σ X0)
       grind)
    | exact superpose eq8 eq47326
    | (have j0 := eq47326 X0
       grind)
    | exact resolve eq47326 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47326
  have eq47418 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq47417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47417
  have eq47722 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq47418 X0
       grind)
    | exact superpose eq47418 eq8
    | exact resolve eq8 eq47418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83656 : x = (k (τ (σ y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq14568
       grind)
    | exact superpose eq14568 eq66
    | exact resolve eq66 eq14568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq14568
  have eq83885 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83656
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83656
    | exact resolve eq83656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83656
  have eq83941 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq83885
       grind)
    | exact superpose eq83885 eq33
    | (have j0 := eq33 y x
       grind)
    | exact resolve eq33 eq83885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq83885
  have eq83953 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq83941
  have eq84451 : x = (k (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19 y x
       have i₂ := eq83953
       grind)
    | exact superpose eq83953 eq19
    | exact resolve eq19 eq83953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq83953
  have eq84546 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84451
       have i₂ := eq17504
       grind)
    | exact superpose eq17504 eq84451
    | exact resolve eq84451 eq17504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17504 eq84451
  have eq84569 : x = (k y x) := by
    first
    | (have j1 := eq171 y x
       grind)
    | (have r₁ := eq84546
       have r₂ := eq171 y x
       grind)
    | exact resolve eq84546 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq84546
  have eq85503 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq465 y x
       have i₂ := eq84569
       grind)
    | exact superpose eq84569 eq465
    | (have j0 := eq465 y x
       grind)
    | exact resolve eq465 eq84569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq84569
  have eq85512 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85503
       have i₂ := eq17508
       grind)
    | exact superpose eq17508 eq85503
    | exact resolve eq85503 eq17508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508 eq85503
  have eq85518 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85512
       have i₂ := eq8 (σ x) (σ x)
       grind)
    | exact superpose eq8 eq85512
    | exact resolve eq85512 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85512
  have eq85519 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq85518
  have eq85523 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85519
       have i₂ := eq47418 x
       grind)
    | exact superpose eq47418 eq85519
    | exact resolve eq85519 eq47418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47418 eq85519
  have eq85904 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq85523
       grind)
    | exact superpose eq85523 eq9
    | exact resolve eq9 eq85523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86083 : y = (M.op x x) := by
    first
    | (have i₁ := eq85904
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq85904
    | exact resolve eq85904 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85904
  have eq86717 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq86083
       grind)
    | exact superpose eq86083 eq8
    | exact resolve eq8 eq86083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86083
  have eq171202 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47722 x
       have i₂ := eq85523
       grind)
    | exact superpose eq85523 eq47722
    | exact resolve eq47722 eq85523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47722 eq85523
  have eq173250 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq171202
       grind)
    | exact superpose eq171202 eq14
    | exact resolve eq14 eq171202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171202
  have eq173484 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq173250
       have i₂ := eq86717
       grind)
    | exact superpose eq86717 eq173250
    | exact resolve eq173250 eq86717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86717 eq173250
  have eq173485 : False := by grind
  exact eq173485

/-- `Equation315`: `x ◇ x = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation315 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law315 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law315.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) := by
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
  have eq19 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq51
  have eq137 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
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
  have eq440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq8
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq8 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq538 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq568 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq538 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq538
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq538 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq568 X0 X1
       grind)
    | exact superpose eq568 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq568 X0 X1
       grind)
    | exact resolve eq33 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq568
  have eq1248 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq4835 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq4984 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4835 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq4835
    | (have j0 := eq4835 X0 X1
       grind)
    | exact resolve eq4835 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq10579 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq440
       have i₂ := eq4984 y x
       grind)
    | exact superpose eq4984 eq440
    | (have j1 := eq4984 (σ y) (σ x)
       grind)
    | (have r₁ := eq440
       have r₂ := eq4984 y x
       grind)
    | exact resolve eq440 eq4984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq4984
  have eq10580 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq10579
  have eq10598 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq137 x
       have i₂ := eq10580
       grind)
    | exact superpose eq10580 eq137
    | exact resolve eq137 eq10580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq10613 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq538 (σ x)
       have i₂ := eq10580
       grind)
    | exact superpose eq10580 eq538
    | exact resolve eq538 eq10580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10580
  have eq10684 : (σ y) = (σ (k y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10613
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq10613
    | exact resolve eq10613 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq10689 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10598
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10598
    | exact resolve eq10598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10598
  have eq10791 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10689
       grind)
    | exact superpose eq10689 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq10689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10689
  have eq10800 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10791
  have eq10938 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq10800
       grind)
    | exact superpose eq10800 eq8
    | exact resolve eq8 eq10800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10800
  have eq12351 : (k y y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq10684
       grind)
    | exact superpose eq10684 eq9
    | exact resolve eq9 eq10684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10684
  have eq12389 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12351
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq12351
    | exact resolve eq12351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12351
  have eq12690 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1248 y y
       have i₂ := eq12389
       grind)
    | exact superpose eq12389 eq1248
    | (have j0 := eq1248 y x
       grind)
    | exact resolve eq1248 eq12389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq12389
  have eq12693 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq12690
  have eq13991 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12693
       have i₂ := eq10938
       grind)
    | exact superpose eq10938 eq12693
    | exact resolve eq12693 eq10938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10938 eq12693
  have eq14050 : y = (M.op x x) := by grind
  clear eq13991
  have eq14657 : x = (k x y) := by grind
  have eq14665 : y = (k y y) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq14050
       grind)
    | exact superpose eq14050 eq538
    | exact resolve eq538 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq14674 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq14050
       grind)
    | exact superpose eq14050 eq8
    | exact resolve eq8 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14050
  have eq15753 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq479 y
       have i₂ := eq14665
       grind)
    | exact superpose eq14665 eq479
    | (have j0 := eq479 y
       grind)
    | exact resolve eq479 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq14665
  have eq15770 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq15753
  have eq18352 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq446 x y
       have i₂ := eq14657
       grind)
    | exact superpose eq14657 eq446
    | (have j0 := eq446 x y
       grind)
    | exact resolve eq446 eq14657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq14657
  have eq18566 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18352
       have i₂ := eq15770
       grind)
    | exact superpose eq15770 eq18352
    | exact resolve eq18352 eq15770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15770 eq18352
  have eq18567 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18566
  have eq20801 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq18567
       grind)
    | exact superpose eq18567 eq8
    | exact resolve eq8 eq18567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18567
  have eq21454 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20801
       grind)
    | exact superpose eq20801 eq14
    | exact resolve eq14 eq20801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20801
  have eq21554 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21454
       have i₂ := eq14674
       grind)
    | exact superpose eq14674 eq21454
    | exact resolve eq21454 eq14674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14674 eq21454
  have eq21555 : False := by grind
  exact eq21555

/-- `Equation323`: `x ◇ y = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation323 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law323 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law323.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
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
  have eq136 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq504 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
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
  have eq564 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq504
    | (have j0 := eq504 X0 X1
       grind)
    | exact resolve eq504 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq619 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
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
  have eq1028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1358 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq148
       have i₂ := eq658 y x
       grind)
    | exact superpose eq658 eq148
    | (have j1 := eq658 y x
       grind)
    | (have r₁ := eq148
       have r₂ := eq658 y x
       grind)
    | exact resolve eq148 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148
       have i₂ := eq564 y x
       grind)
    | exact superpose eq564 eq148
    | (have j1 := eq564 (σ y) (σ x)
       grind)
    | (have r₁ := eq148
       have r₂ := eq564 y x
       grind)
    | exact resolve eq148 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1360 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1359
  have eq1361 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1358
  have eq1374 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq123 x
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq123
    | exact resolve eq123 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1380 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq8
    | exact resolve eq8 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1374
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1374
    | exact resolve eq1374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1460 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq564 y x
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq564
    | (have j0 := eq564 y x
       grind)
    | exact resolve eq564 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1384
  have eq1466 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1464
  have eq1467 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1460
  have eq1516 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1526 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq175 x y
       have i₂ := eq1467
       grind)
    | exact superpose eq1467 eq175
    | (have r₁ := eq175 x y
       have r₂ := eq1467
       grind)
    | exact resolve eq175 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1467
  have eq1530 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1526
  have eq1636 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | (have j0 := eq136 X1 (τ X0)
       grind)
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1738 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1636 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1636
    | (have j0 := eq1636 X0 X1
       grind)
    | exact resolve eq1636 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1636
  have eq1748 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1738 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1738
    | (have j0 := eq1738 X0 X1
       grind)
    | exact resolve eq1738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1994 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq151 x x
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq151
    | (have j0 := eq151 x x
       grind)
    | exact resolve eq151 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq1530
  have eq1997 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1994
  have eq3649 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq123 x
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq123
    | exact resolve eq123 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1361
  have eq3659 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3649
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3649
    | exact resolve eq3649 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq3660 : x = (k x y) := by grind
  clear eq3659
  have eq4075 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4518 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq4075
  have eq7150 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1380
       grind)
    | exact superpose eq1380 eq14
    | exact resolve eq14 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq7772 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7150
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq7150
    | exact resolve eq7150 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq7150
  have eq7773 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq7772
  have eq8885 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1360
       have i₂ := eq1997
       grind)
    | exact superpose eq1997 eq1360
    | exact resolve eq1360 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq1997
  have eq8910 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq8885
  have eq8924 : y = (M.op x x) := by
    first
    | (have r₁ := eq8910
       have r₂ := eq7773
       grind)
    | exact resolve eq8910 eq7773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7773 eq8910
  have eq9069 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq8
    | exact resolve eq8 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9100 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1516 x y
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq1516
    | (have j0 := eq1516 x y
       grind)
    | exact resolve eq1516 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq9482 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3660
       have i₂ := eq1748 x y
       grind)
    | exact superpose eq1748 eq3660
    | (have j1 := eq1748 x y
       grind)
    | exact resolve eq3660 eq1748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748 eq3660
  have eq9585 : x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq9482
       have r₂ := eq4518
       grind)
    | exact resolve eq9482 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq9482
  have eq9621 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq9585
       have i₂ := eq9069
       grind)
    | exact superpose eq9069 eq9585
    | exact resolve eq9585 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585
  have eq15395 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1028 x x
       have i₂ := eq9621
       grind)
    | exact superpose eq9621 eq1028
    | exact resolve eq1028 eq9621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq9621
  have eq15468 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq15395
       have r₂ := eq9100
       grind)
    | exact resolve eq15395 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15395
  have eq15496 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15468
       grind)
    | exact superpose eq15468 eq14
    | exact resolve eq14 eq15468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq15525 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15496
       have i₂ := eq9069
       grind)
    | exact superpose eq9069 eq15496
    | exact resolve eq15496 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9069 eq15496
  have eq15526 : x = y := by grind
  clear eq15525
  have eq15925 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq14
    | exact resolve eq14 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15950 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9100
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq9100
    | exact resolve eq9100 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100
  have eq15953 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq15950
  have eq15965 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15925
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq15925
    | exact resolve eq15925 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924 eq15925
  have eq15966 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq15965
       have i₂ := eq15953
       grind)
    | exact superpose eq15953 eq15965
    | exact resolve eq15965 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15953 eq15965
  have eq15967 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15966
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq15966
    | exact resolve eq15966 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15526 eq15966
  have eq15968 : False := by grind
  exact eq15968

/-- `Equation323`: `x ◇ y = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation323 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law323 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law323.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq44 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq25 (τ X1) X0
       grind)
    | exact superpose eq25 eq17
    | (have j1 := eq25 (τ X1) X0
       grind)
    | exact resolve eq17 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq51 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq22
  have eq59 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq26 (σ X1) (σ X0)
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X1 X0
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq177 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X0 X1) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 X1 X0
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq508 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq508
    | (have j0 := eq508 X0 X1
       grind)
    | exact resolve eq508 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq624 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq1033 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1365 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq150
       have i₂ := eq663 y x
       grind)
    | exact superpose eq663 eq150
    | (have j1 := eq663 y x
       grind)
    | (have r₁ := eq150
       have r₂ := eq663 y x
       grind)
    | exact resolve eq150 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq150
       have i₂ := eq568 y x
       grind)
    | exact superpose eq568 eq150
    | (have j1 := eq568 (σ y) (σ x)
       grind)
    | (have r₁ := eq150
       have r₂ := eq568 y x
       grind)
    | exact resolve eq150 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq1367 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1366
  have eq1368 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq1365
  have eq1381 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq1367
       grind)
    | exact superpose eq1367 eq59
    | exact resolve eq59 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1387 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1367
       grind)
    | exact superpose eq1367 eq8
    | exact resolve eq8 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1391 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1381
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1381
    | exact resolve eq1381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1468 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1391
       grind)
    | exact superpose eq1391 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq568 y x
       have i₂ := eq1391
       grind)
    | exact superpose eq1391 eq568
    | (have j0 := eq568 y x
       grind)
    | exact resolve eq568 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq1391
  have eq1474 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1472
  have eq1475 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1468
  have eq1524 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1534 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq1475
       grind)
    | exact superpose eq1475 eq177
    | (have r₁ := eq177 x y
       have r₂ := eq1475
       grind)
    | exact resolve eq177 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1475
  have eq1538 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1534
  have eq1644 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138
    | (have j0 := eq138 X1 (τ X0)
       grind)
    | exact resolve eq138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1746 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1644 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1644
    | (have j0 := eq1644 X0 X1
       grind)
    | exact resolve eq1644 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1644
  have eq1756 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1746 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1746
    | (have j0 := eq1746 X0 X1
       grind)
    | exact resolve eq1746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq2002 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153 x x
       have i₂ := eq1538
       grind)
    | exact superpose eq1538 eq153
    | (have j0 := eq153 x x
       grind)
    | exact resolve eq153 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1538
  have eq2005 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2002
  have eq3656 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq1368
       grind)
    | exact superpose eq1368 eq59
    | exact resolve eq59 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1368
  have eq3666 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3656
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3656
    | exact resolve eq3656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq3667 : x = (k y x) := by grind
  clear eq3666
  have eq4096 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 y x
       have i₂ := eq3667
       grind)
    | exact superpose eq3667 eq26
    | (have j0 := eq26 y x
       grind)
    | exact resolve eq26 eq3667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4525 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq4096
  have eq7155 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1387
       grind)
    | exact superpose eq1387 eq14
    | exact resolve eq14 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq7777 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7155
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq7155
    | exact resolve eq7155 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq7155
  have eq7778 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq7777
  have eq8693 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1367
       have i₂ := eq2005
       grind)
    | exact superpose eq2005 eq1367
    | exact resolve eq1367 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367 eq2005
  have eq8718 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq8693
  have eq8730 : y = (M.op x x) := by
    first
    | (have r₁ := eq8718
       have r₂ := eq7778
       grind)
    | exact resolve eq8718 eq7778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7778 eq8718
  have eq8890 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq8730
       grind)
    | exact superpose eq8730 eq8
    | exact resolve eq8 eq8730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9067 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1524 x y
       have i₂ := eq3667
       grind)
    | exact superpose eq3667 eq1524
    | (have j0 := eq1524 x y
       grind)
    | exact resolve eq1524 eq3667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq9511 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3667
       have i₂ := eq1756 x y
       grind)
    | exact superpose eq1756 eq3667
    | (have j1 := eq1756 x y
       grind)
    | exact resolve eq3667 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756 eq3667
  have eq9618 : x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq9511
       have r₂ := eq4525
       grind)
    | exact resolve eq9511 eq4525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525 eq9511
  have eq9653 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq9618
       have i₂ := eq8890
       grind)
    | exact superpose eq8890 eq9618
    | exact resolve eq9618 eq8890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9618
  have eq15430 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1033 x x
       have i₂ := eq9653
       grind)
    | exact superpose eq9653 eq1033
    | exact resolve eq1033 eq9653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq9653
  have eq15503 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq15430
       have r₂ := eq9067
       grind)
    | exact resolve eq15430 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15430
  have eq15530 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15503
       grind)
    | exact superpose eq15503 eq14
    | exact resolve eq14 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq15559 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15530
       have i₂ := eq8890
       grind)
    | exact superpose eq8890 eq15530
    | exact resolve eq15530 eq8890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8890 eq15530
  have eq15560 : x = y := by grind
  clear eq15559
  have eq15964 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15560
       grind)
    | exact superpose eq15560 eq14
    | exact resolve eq14 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15989 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9067
       have i₂ := eq15560
       grind)
    | exact superpose eq15560 eq9067
    | exact resolve eq9067 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067
  have eq15992 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq15989
  have eq16004 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15964
       have i₂ := eq8730
       grind)
    | exact superpose eq8730 eq15964
    | exact resolve eq15964 eq8730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8730 eq15964
  have eq16005 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq16004
       have i₂ := eq15992
       grind)
    | exact superpose eq15992 eq16004
    | exact resolve eq16004 eq15992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15992 eq16004
  have eq16006 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq16005
       have i₂ := eq15560
       grind)
    | exact superpose eq15560 eq16005
    | exact resolve eq16005 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560 eq16005
  have eq16007 : False := by grind
  exact eq16007

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation325 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law325 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
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
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X0) (σ X1)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
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
  have eq102 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq117 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
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
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq45 (M.op X0 X0) X0
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq29
    | (have j0 := eq29 X0 X1
       have j1 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X0
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq16
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq16 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq117
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq117 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq244 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq117 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq117
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq117 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq650 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq188
    | (have j0 := eq188 (τ X0)
       grind)
    | exact resolve eq188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq650 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq650
    | (have j0 := eq650 X0
       grind)
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq655 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq652 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | (have j0 := eq652 X0
       grind)
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq668 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
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
  have eq699 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
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
  clear eq32
  have eq747 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq668
    | (have j0 := eq668 X0 X1
       grind)
    | exact resolve eq668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq769 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq655 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq655
    | (have j0 := eq655 (τ X0)
       grind)
    | exact resolve eq655 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq772 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq815 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1203 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 y x
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 y x
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq40 X0 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1873 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq40
    | (have j0 := eq40 X1 X0
       have j1 := eq62 X0 X1
       grind)
    | exact resolve eq40 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq62
  have eq1887 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq2498 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | (have j0 := eq66 X1 (σ X0)
       grind)
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2517 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq66 (τ X0) X0
       grind)
    | exact superpose eq66 eq188
    | (have j0 := eq188 (τ X0)
       have j1 := eq66 (τ X0) X0
       grind)
    | exact resolve eq188 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2558 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2517 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2517
    | (have j0 := eq2517 X0
       grind)
    | exact resolve eq2517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2569 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2498 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2498
    | (have j0 := eq2498 X0 X1
       grind)
    | exact resolve eq2498 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2582 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2558 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2558
    | (have j0 := eq2558 X0
       grind)
    | exact resolve eq2558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2598 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq2582 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2582
    | (have j0 := eq2582 X0
       grind)
    | exact resolve eq2582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582
  have eq2611 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2598 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq2598 X0
       have r₂ := eq45 X0 X0
       grind)
    | exact resolve eq2598 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2626 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155
    | (have j0 := eq155 X1 (τ X0)
       grind)
    | exact resolve eq155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2752 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2626 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2626
    | (have j0 := eq2626 X0 X1
       grind)
    | exact resolve eq2626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2626
  have eq2763 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2752
    | (have j0 := eq2752 X0 X1
       grind)
    | exact resolve eq2752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq2777 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2611 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2611
    | (have j0 := eq2611 (σ X0)
       grind)
    | exact resolve eq2611 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq2803 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2777 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq2777
    | (have j0 := eq2777 X0
       grind)
    | exact resolve eq2777 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq3015 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq2569 X0 X0
       grind)
    | exact superpose eq2569 eq188
    | (have j0 := eq188 X0
       have j1 := eq2569 X0 X0
       grind)
    | (have r₁ := eq188 x
       have r₂ := eq2569 x x
       grind)
    | exact resolve eq188 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3051 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3098 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq3114 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq172
    | (have j0 := eq172 (τ X0) (τ X1)
       grind)
    | exact resolve eq172 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq3146 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3114 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3114
    | (have j0 := eq3114 X0 X1
       grind)
    | exact resolve eq3114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3153 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3146 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3146
    | (have j0 := eq3146 X0 X1
       grind)
    | exact resolve eq3146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146
  have eq3155 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3153 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3153
    | (have j0 := eq3153 X0 X1
       grind)
    | exact resolve eq3153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3156 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3155 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3155
    | (have j0 := eq3155 X0 X1
       grind)
    | exact resolve eq3155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3157 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3156 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3156
    | (have j0 := eq3156 X0 X1
       grind)
    | exact resolve eq3156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3346 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3347 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3923 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq154 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq9
    | (have j1 := eq154 X0 X1
       grind)
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3978 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3923 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3923
    | (have j0 := eq3923 X0 X1
       grind)
    | exact resolve eq3923 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq8629 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq244
    | (have j0 := eq244 X1 (τ X0)
       grind)
    | exact resolve eq244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8761 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8629 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq8629
    | (have j0 := eq8629 X0 X1
       grind)
    | exact resolve eq8629 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq9800 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq9848 : y = (k y x) := by
    first
    | (have j1 := eq815 x y
       grind)
    | (have r₁ := eq9800
       have r₂ := eq815 x y
       grind)
    | exact resolve eq9800 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9800
  have eq10496 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq747 x y
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq747
    | (have j0 := eq747 x y
       grind)
    | exact resolve eq747 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10498 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3157 y x
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq3157
    | (have j0 := eq3157 y (M.op y x)
       grind)
    | exact resolve eq3157 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq13298 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq143 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq143 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13338 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq143 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq13351 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13298
  have eq14294 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq699 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq14295 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14294 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14294
    | (have j0 := eq14294 X0
       grind)
    | exact resolve eq14294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14294
  have eq14401 : x ≠ (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq10498
  have eq14410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1203
       have i₂ := eq13351 x y
       grind)
    | exact superpose eq13351 eq1203
    | (have j1 := eq13351 x y
       grind)
    | exact resolve eq1203 eq13351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq13351
  have eq14419 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq14410
  have eq15771 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14295 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq14295
    | (have j0 := eq14295 (σ X0)
       grind)
    | exact resolve eq14295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14295
  have eq15783 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15771 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15771
    | (have j0 := eq15771 X0
       grind)
    | exact resolve eq15771 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq16154 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1887 x y
       grind)
    | exact superpose eq1887 eq14
    | (have j1 := eq1887 x y
       grind)
    | exact resolve eq14 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq16239 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16154
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq16154
    | exact resolve eq16154 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq19492 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16239
       have i₂ := eq14419
       grind)
    | exact superpose eq14419 eq16239
    | (have r₁ := eq16239
       have r₂ := eq14419
       grind)
    | exact resolve eq16239 eq14419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419 eq16239
  have eq19498 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by grind
  clear eq19492
  have eq19842 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq19498
       grind)
    | exact superpose eq19498 eq9
    | exact resolve eq9 eq19498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq19954 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq19842
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq19842
    | exact resolve eq19842 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842
  have eq19955 : x = (k x y) := by grind
  clear eq19954
  have eq20068 : y = (k x x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2763 x y
       have i₂ := eq19955
       grind)
    | exact superpose eq19955 eq2763
    | (have j0 := eq2763 x y
       grind)
    | exact resolve eq2763 eq19955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq25227 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15783 X0
       have i₂ := eq2569 X0 X0
       grind)
    | exact superpose eq2569 eq15783
    | (have j0 := eq15783 X0
       have j1 := eq2569 X0 X0
       grind)
    | (have r₁ := eq15783 x
       have r₂ := eq2569 x x
       grind)
    | exact resolve eq15783 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25244 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25227
  have eq27439 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25244 X1
       have i₂ := eq747 X0 X1
       grind)
    | (have i₁ := eq25244 X0
       have i₂ := eq747 (M.op X0 X0) X1
       grind)
    | exact superpose eq747 eq25244
    | (have j1 := eq747 X0 X1
       grind)
    | exact resolve eq25244 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq25244
  have eq35678 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq769 (σ X0)
       have i₂ := eq244 (σ X0) X0
       grind)
    | exact superpose eq244 eq769
    | (have j0 := eq769 (σ X0)
       have j1 := eq244 (σ X0) X0
       grind)
    | exact resolve eq769 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq35691 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq769 X0
       have i₂ := eq8761 X0 X0
       grind)
    | exact superpose eq8761 eq769
    | (have j0 := eq769 X0
       have j1 := eq8761 X0 X0
       grind)
    | (have r₁ := eq769 x
       have r₂ := eq8761 x x
       grind)
    | exact resolve eq769 eq8761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq8761
  have eq35700 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq35691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35691
  have eq35709 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35678 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35678
    | (have j0 := eq35678 X0
       grind)
    | exact resolve eq35678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35678
  have eq35723 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35709 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35709
    | (have j0 := eq35709 X0
       grind)
    | exact resolve eq35709 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35709
  have eq35730 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq35723 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35723
    | (have j0 := eq35723 X0
       grind)
    | exact resolve eq35723 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35723
  have eq35735 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq35730 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq35730 X0
       have r₂ := eq45 X0 X0
       grind)
    | exact resolve eq35730 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq35730
  have eq41263 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3346 (τ X0) (τ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq3346
    | exact resolve eq3346 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3346
  have eq41330 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41263 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41263
    | (have j0 := eq41263 X0 X1
       grind)
    | exact resolve eq41263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41263
  have eq41358 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41330 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq41330
    | (have j0 := eq41330 X0 X1
       grind)
    | exact resolve eq41330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41330
  have eq41372 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41358 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41358
    | (have j0 := eq41358 X0 X1
       grind)
    | exact resolve eq41358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41358
  have eq41377 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41372 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq41372
    | (have j0 := eq41372 X0 X1
       grind)
    | exact resolve eq41372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41372
  have eq41378 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41377 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq41377
    | (have j0 := eq41377 X0 X1
       grind)
    | exact resolve eq41377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41377
  have eq41401 : x ≠ (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41378 x y
       have i₂ := eq19955
       grind)
    | exact superpose eq19955 eq41378
    | exact resolve eq41378 eq19955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41378
  have eq41649 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3978 x y
       grind)
    | exact superpose eq3978 eq14
    | (have j1 := eq3978 x y
       grind)
    | exact resolve eq14 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978
  have eq41910 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq27439 x y
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 x y
       grind)
    | exact resolve eq41649 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27439 eq41649
  have eq42131 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2569 y y
       have i₂ := eq41910
       grind)
    | exact superpose eq41910 eq2569
    | exact resolve eq2569 eq41910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq41910
  have eq42144 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq42131
  have eq42986 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq42144
       grind)
    | exact superpose eq42144 eq8
    | exact resolve eq8 eq42144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42144
  have eq59601 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35700 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35700
    | (have j0 := eq35700 (σ X0)
       grind)
    | exact resolve eq35700 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35700
  have eq59691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59601 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq59601
    | (have j0 := eq59601 X0
       grind)
    | exact resolve eq59601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59601
  have eq60038 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3347 X0 (M.op X0 X0)
       have i₂ := eq13338 X0
       grind)
    | exact superpose eq13338 eq3347
    | (have j0 := eq3347 X0 (M.op X0 X0)
       grind)
    | exact resolve eq3347 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347 eq13338
  have eq60041 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq60038 X0
       have j1 := eq3098 X0
       grind)
    | (have r₁ := eq60038 X0
       have r₂ := eq3098 X0
       grind)
    | exact resolve eq60038 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098 eq60038
  have eq65727 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq65783 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65727 X0 X1
       have j1 := eq155 X1 X0
       grind)
    | (have r₁ := eq65727 (k X1 X1) X0
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq65727 X0 (σ (k X1 X1))
       have r₂ := eq155 (σ X0) X1
       grind)
    | (have r₁ := eq65727 X1 X0
       have r₂ := eq155 X0 X1
       grind)
    | exact resolve eq65727 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq65727
  have eq65840 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq65783 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq65783 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq65783 eq17
    | (have j1 := eq65783 (τ X1) X0
       grind)
    | exact resolve eq17 eq65783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65841 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq65783 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq65783 X0 (σ X0)
       grind)
    | exact superpose eq65783 eq9
    | (have j1 := eq65783 X1 X0
       grind)
    | exact resolve eq9 eq65783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65783
  have eq65897 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq65840 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq65840
    | (have j0 := eq65840 X0 X1
       grind)
    | exact resolve eq65840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65840
  have eq65907 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65897 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65897
    | (have j0 := eq65897 X0 X1
       grind)
    | exact resolve eq65897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65897
  have eq66366 : y = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19955
       have i₂ := eq65907 y x
       grind)
    | exact superpose eq65907 eq19955
    | (have j1 := eq65907 y x
       grind)
    | exact resolve eq19955 eq65907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19955 eq65907
  have eq67288 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq15783 x
       have i₂ := eq66366
       grind)
    | exact superpose eq66366 eq15783
    | (have j0 := eq15783 x
       grind)
    | exact resolve eq15783 eq66366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66366
  have eq67330 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq67288
       have r₂ := eq42986
       grind)
    | exact resolve eq67288 eq42986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42986 eq67288
  have eq67572 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2803 x
       have i₂ := eq67330
       grind)
    | exact superpose eq67330 eq2803
    | (have j0 := eq2803 x
       grind)
    | (have r₁ := eq2803 x
       have r₂ := eq67330
       grind)
    | exact resolve eq2803 eq67330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803 eq67330
  have eq67628 : (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by grind
  clear eq67572
  have eq70277 : (k x x) = (τ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq67628
       grind)
    | exact superpose eq67628 eq9
    | exact resolve eq9 eq67628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67628
  have eq70356 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq70277
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70277
    | exact resolve eq70277 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70277
  have eq70411 : x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20068
       have i₂ := eq70356
       grind)
    | exact superpose eq70356 eq20068
    | exact resolve eq20068 eq70356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068 eq70356
  have eq70467 : x = (M.op y x) ∨ x = y := by grind
  clear eq70411
  have eq71031 : x ≠ x ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14401
       have i₂ := eq70467
       grind)
    | exact superpose eq70467 eq14401
    | (have r₁ := eq14401
       have r₂ := eq70467
       grind)
    | exact resolve eq14401 eq70467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14401
  have eq71067 : x = (M.op y y) ∨ x = y := by grind
  clear eq71031
  have eq102445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq65841 (σ X0) X1
       grind)
    | exact superpose eq65841 eq13
    | (have j1 := eq65841 (σ X0) X1
       grind)
    | exact resolve eq13 eq65841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65841
  have eq102469 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102445 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq102445
    | (have j0 := eq102445 X0 X1
       grind)
    | exact resolve eq102445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102445
  have eq108875 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102469 x y
       grind)
    | exact superpose eq102469 eq14
    | (have j1 := eq102469 x y
       grind)
    | exact resolve eq14 eq102469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108931 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq108875
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq108875
    | exact resolve eq108875 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq108875
  have eq110153 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108931
       have i₂ := eq10496
       grind)
    | exact superpose eq10496 eq108931
    | (have r₁ := eq108931
       have r₂ := eq10496
       grind)
    | exact resolve eq108931 eq10496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496 eq108931
  have eq110156 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq110153
  have eq111995 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq110156
       grind)
    | exact superpose eq110156 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq110156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110156
  have eq112040 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq111995
  have eq114041 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41401
       have i₂ := eq112040
       grind)
    | exact superpose eq112040 eq41401
    | (have r₁ := eq41401
       have r₂ := eq112040
       grind)
    | exact resolve eq41401 eq112040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114102 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq112040
  have eq114118 : x = (M.op y y) := by
    first
    | (have r₁ := eq114102
       have r₂ := eq71067
       grind)
    | exact resolve eq114102 eq71067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71067 eq114102
  have eq114124 : x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq114041
       have r₂ := eq70467
       grind)
    | exact resolve eq114041 eq70467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70467 eq114041
  have eq114126 : x = (M.op y x) := by
    first
    | (have r₁ := eq114124
       have r₂ := eq41401
       grind)
    | exact resolve eq114124 eq41401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41401 eq114124
  have eq115003 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq60041 y
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq60041
    | exact resolve eq60041 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60041
  have eq115007 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16 y y
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq16
    | exact resolve eq16 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq122836 : (σ y) = (M.op (σ y) (σ x)) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq3051 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq3051
    | (have j0 := eq3051 y
       grind)
    | exact resolve eq3051 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq122849 : y ≠ (τ (M.op (σ y) (σ x))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq35735 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq35735
    | (have j0 := eq35735 y
       grind)
    | exact resolve eq35735 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35735
  have eq122850 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq59691 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq59691
    | (have j0 := eq59691 y
       grind)
    | exact resolve eq59691 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59691
  have eq122899 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq8 (σ y) (σ y)
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq8
    | exact resolve eq8 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122924 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq122850
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq122850
    | exact resolve eq122850 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122850
  have eq122925 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq122836
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq122836
    | exact resolve eq122836 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122836
  have eq162407 : y ≠ (τ (σ y)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq122849
       have i₂ := eq122925
       grind)
    | exact superpose eq122925 eq122849
    | exact resolve eq122849 eq122925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122849 eq122925
  have eq162457 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq162407
       have r₂ := eq9 y
       grind)
    | exact resolve eq162407 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162407
  have eq163956 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq162457
       grind)
    | exact superpose eq162457 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq162457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq163964 : x ≠ y ∨ x = (k y y) := by grind
  clear eq162457
  have eq163965 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq163956
  have eq163987 : x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq163965
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq163965
    | exact resolve eq163965 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114118 eq163965
  have eq164010 : x = (k y y) := by
    first
    | (have r₁ := eq163987
       have r₂ := eq163964
       grind)
    | exact resolve eq163987 eq163964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163964 eq163987
  have eq165381 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq164010
       grind)
    | exact superpose eq164010 eq188
    | (have j0 := eq188 y
       grind)
    | exact resolve eq188 eq164010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165472 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq165381
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq165381
    | exact resolve eq165381 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115003 eq165381
  have eq183529 : (σ (k y y)) = (M.op (σ y) (σ (k y y))) ∨ x = y := by
    first
    | (have i₁ := eq122899
       have i₂ := eq122924
       grind)
    | exact superpose eq122924 eq122899
    | exact resolve eq122899 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122899 eq122924
  have eq183550 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq183529
       have i₂ := eq164010
       grind)
    | exact superpose eq164010 eq183529
    | exact resolve eq183529 eq164010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164010 eq183529
  have eq184343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 (σ x) (σ y)
       have i₂ := eq183550
       grind)
    | exact superpose eq183550 eq8
    | exact resolve eq8 eq183550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183550
  have eq196164 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq184343
       grind)
    | exact superpose eq184343 eq14
    | exact resolve eq14 eq184343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184343
  have eq196194 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq196164
       have i₂ := eq115007
       grind)
    | exact superpose eq115007 eq196164
    | exact resolve eq196164 eq115007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115007 eq196164
  have eq197066 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq196194
       have i₂ := eq102469 x x
       grind)
    | exact superpose eq102469 eq196194
    | (have j1 := eq102469 x x
       grind)
    | exact resolve eq196194 eq102469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102469
  have eq197070 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq815 x x
       grind)
    | (have r₁ := eq197066
       have r₂ := eq815 x x
       grind)
    | exact resolve eq197066 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq197066
  have eq197642 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq197070
       grind)
    | exact superpose eq197070 eq188
    | (have j0 := eq188 x
       grind)
    | exact resolve eq188 eq197070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq197665 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15783 x
       have i₂ := eq197070
       grind)
    | exact superpose eq197070 eq15783
    | (have j0 := eq15783 x
       grind)
    | exact resolve eq15783 eq197070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15783 eq197070
  have eq197690 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq197665
  have eq197699 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq197642
  have eq208083 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq196194
       have i₂ := eq197699
       grind)
    | exact superpose eq197699 eq196194
    | exact resolve eq196194 eq197699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196194 eq197699
  have eq208172 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq208083
  have eq208208 : x = y := by
    first
    | (have r₁ := eq208172
       have r₂ := eq197690
       grind)
    | exact resolve eq208172 eq197690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197690 eq208172
  have eq209365 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq14
    | exact resolve eq14 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209443 : x = (M.op x x) := by
    first
    | (have i₁ := eq114126
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq114126
    | exact resolve eq114126 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114126
  have eq209481 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq165472
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq165472
    | exact resolve eq165472 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165472 eq208208
  have eq209487 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq209481
  have eq209524 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq209365
       have i₂ := eq209443
       grind)
    | exact superpose eq209443 eq209365
    | exact resolve eq209365 eq209443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209365 eq209443
  have eq209531 : False := by grind
  exact eq209531

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation325 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law325 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
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
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq50 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq22
  have eq58 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X0) (σ X1)
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq36
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq144 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq45 X0 (M.op X0 X0)
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq27 X0 X1
       grind)
    | exact resolve eq27 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1) (σ X1)
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq16
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq189 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq27 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq58
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq245 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | (have i₁ := eq58 X0
       have i₂ := eq12 (M.op (σ X0) (σ X0)) X1
       grind)
    | exact superpose eq12 eq58
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq652 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq189 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq189
    | (have j0 := eq189 (τ X0)
       grind)
    | exact resolve eq189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq654 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq652 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | (have j0 := eq652 X0
       grind)
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq657 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq654 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq654
    | (have j0 := eq654 X0
       grind)
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq670 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28
    | exact resolve eq28 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq10
    | (have j1 := eq28 X1 X0
       grind)
    | exact resolve eq10 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq670
    | (have j0 := eq670 X0 X1
       grind)
    | exact resolve eq670 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq774 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq817 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq877 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq749 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq749 (M.op X1 X0) X1
       grind)
    | exact superpose eq749 eq8
    | (have j1 := eq749 X0 X1
       grind)
    | exact resolve eq8 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq40 X0 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1878 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq40
    | (have j0 := eq40 X0 X1
       have j1 := eq64 X0 X1
       grind)
    | exact resolve eq40 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1892 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1878 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq3154 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq100 X1 (σ X0)
       grind)
    | exact superpose eq100 eq13
    | (have j1 := eq100 X1 (σ X0)
       grind)
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3165 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq657 (σ X0)
       have i₂ := eq100 X0 (σ X0)
       grind)
    | exact superpose eq100 eq657
    | (have j0 := eq657 (σ X0)
       have j1 := eq100 X0 (σ X0)
       grind)
    | (have r₁ := eq657 (σ X0)
       have r₂ := eq100 X0 (σ X0)
       grind)
    | exact resolve eq657 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3185 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq3198 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3185 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3185
    | (have j0 := eq3185 X0
       grind)
    | exact resolve eq3185 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3204 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3154 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3154
    | (have j0 := eq3154 X0 X1
       grind)
    | exact resolve eq3154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3251 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq3260 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq173 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq173
    | (have j0 := eq173 (τ X0) (τ X1)
       grind)
    | exact resolve eq173 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq3296 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3260 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3260
    | (have j0 := eq3260 X0 X1
       grind)
    | exact resolve eq3260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq3302 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3296
    | (have j0 := eq3296 X0 X1
       grind)
    | exact resolve eq3296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3303 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3302 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3302
    | (have j0 := eq3302 X0 X1
       grind)
    | exact resolve eq3302 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3304 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3303 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3303
    | (have j0 := eq3303 X0 X1
       grind)
    | exact resolve eq3303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3305 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3304 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3304
    | (have j0 := eq3304 X0 X1
       grind)
    | exact resolve eq3304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3471 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq14
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq14 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3531 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq3971 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq155 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq9
    | (have j1 := eq155 X0 X1
       grind)
    | exact resolve eq9 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq4030 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3971 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3971
    | (have j0 := eq3971 X0 X1
       grind)
    | exact resolve eq3971 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971
  have eq7385 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq657 (τ X0)
       have i₂ := eq245 X0 (τ X0)
       grind)
    | exact superpose eq245 eq657
    | (have j0 := eq657 (τ X0)
       have j1 := eq245 X0 (τ X0)
       grind)
    | (have r₁ := eq657 (τ X0)
       have r₂ := eq245 X0 (τ X0)
       grind)
    | exact resolve eq657 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq657
  have eq7420 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
    intro X0
    first
    | (have j0 := eq7385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7385
  have eq7441 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7420 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7420
    | (have j0 := eq7420 X0
       grind)
    | exact resolve eq7420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7420
  have eq8743 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq264 x y
       grind)
    | exact superpose eq264 eq14
    | (have j1 := eq264 x y
       grind)
    | exact resolve eq14 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq8788 : y = (k x y) := by
    first
    | (have j1 := eq817 x y
       grind)
    | (have r₁ := eq8743
       have r₂ := eq817 x y
       grind)
    | exact resolve eq8743 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8743
  have eq9000 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq877 x y
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq877
    | (have j0 := eq877 x y
       grind)
    | exact resolve eq877 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq9001 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3305 x y
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq3305
    | (have j0 := eq3305 (M.op y x) y
       grind)
    | exact resolve eq3305 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12908 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq72 X0 (σ X1)
       grind)
    | exact superpose eq72 eq58
    | (have j1 := eq72 X0 (σ X1)
       grind)
    | exact resolve eq58 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq12956 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12908 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12908
    | (have j0 := eq12908 X0 X1
       grind)
    | exact resolve eq12908 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12908
  have eq13078 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12956 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq12956
    | (have j0 := eq12956 X0 X1
       grind)
    | exact resolve eq12956 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12956
  have eq13124 : x ≠ (M.op y x) ∨ x = (M.op y y) := by grind
  have eq13171 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X1 X1
       have i₂ := eq749 X0 X1
       grind)
    | (have i₁ := eq144 X0 X1
       have i₂ := eq749 (M.op X1 X0) X1
       grind)
    | exact superpose eq749 eq144
    | (have j1 := eq749 X0 X1
       grind)
    | (have r₁ := eq144 X1 X1
       have r₂ := eq749 (M.op X1 X1) X1
       grind)
    | exact resolve eq144 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13215 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq144 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq13232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13171 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13171
  have eq14098 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq701 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq14099 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14098 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14098
    | (have j0 := eq14098 X0
       grind)
    | exact resolve eq14098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14098
  have eq14827 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14099 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq14099
    | (have j0 := eq14099 (σ X0)
       grind)
    | exact resolve eq14099 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14829 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14099 (σ X0)
       have i₂ := eq100 X0 (σ X0)
       grind)
    | exact superpose eq100 eq14099
    | (have j0 := eq14099 (σ X0)
       have j1 := eq100 X0 (σ X0)
       grind)
    | (have r₁ := eq14099 (σ X0)
       have r₂ := eq100 X0 (σ X0)
       grind)
    | exact resolve eq14099 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq14099
  have eq14833 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq14829 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14829
  have eq14835 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14833 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14833
    | (have j0 := eq14833 X0
       grind)
    | exact resolve eq14833 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14833
  have eq14837 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14827 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14827
    | (have j0 := eq14827 X0
       grind)
    | exact resolve eq14827 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq14843 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq14835 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14835
    | (have j0 := eq14835 X0
       grind)
    | exact resolve eq14835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14835
  have eq15930 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1892 x y
       grind)
    | exact superpose eq1892 eq14
    | (have j1 := eq1892 x y
       grind)
    | exact resolve eq14 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq16013 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq15930
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq15930
    | exact resolve eq15930 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15930
  have eq17565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq13232 x y
       grind)
    | exact superpose eq13232 eq1205
    | (have j1 := eq13232 x y
       grind)
    | (have r₁ := eq1205
       have r₂ := eq13232 x y
       grind)
    | exact resolve eq1205 eq13232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq13232
  have eq17670 : (σ (M.op x y)) = (σ y) ∨ x = (k y x) := by grind
  clear eq17565
  have eq18665 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16013
       have i₂ := eq17670
       grind)
    | exact superpose eq17670 eq16013
    | (have r₁ := eq16013
       have r₂ := eq17670
       grind)
    | exact resolve eq16013 eq17670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16013 eq17670
  have eq18671 : (σ x) = (σ (k y x)) ∨ x = (k y x) := by grind
  clear eq18665
  have eq18830 : (k y x) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq18671
       grind)
    | exact superpose eq18671 eq9
    | exact resolve eq9 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671
  have eq18940 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq18830
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18830
    | exact resolve eq18830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18830
  have eq18941 : x = (k y x) := by grind
  clear eq18940
  have eq19399 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3305 y x
       have i₂ := eq18941
       grind)
    | exact superpose eq18941 eq3305
    | (have j0 := eq3305 (M.op x y) x
       grind)
    | exact resolve eq3305 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq24663 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14843 X1
       have i₂ := eq749 X0 X1
       grind)
    | (have i₁ := eq14843 X0
       have i₂ := eq749 (M.op X0 X0) X1
       grind)
    | exact superpose eq749 eq14843
    | (have j1 := eq749 X0 X1
       grind)
    | exact resolve eq14843 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq37657 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13078 X1 X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13078
    | (have j0 := eq13078 X1 X0
       have j1 := eq64 X0 X1
       grind)
    | exact resolve eq13078 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq13078
  have eq37815 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37657 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37657
    | (have j0 := eq37657 X0 X1
       grind)
    | exact resolve eq37657 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37657
  have eq37816 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37815 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37815
  have eq41946 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4030 x y
       grind)
    | exact superpose eq4030 eq14
    | (have j1 := eq4030 x y
       grind)
    | exact resolve eq14 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq42207 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq24663 x y
       grind)
    | (have r₁ := eq41946
       have r₂ := eq24663 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq41946
       have r₂ := eq24663 (k x y) (M.op x y)
       grind)
    | (have r₁ := eq41946
       have r₂ := eq24663 x y
       grind)
    | exact resolve eq41946 eq24663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24663 eq41946
  have eq42430 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3204 y y
       have i₂ := eq42207
       grind)
    | exact superpose eq42207 eq3204
    | exact resolve eq3204 eq42207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204 eq42207
  have eq42443 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq42430
  have eq43291 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq42443
       grind)
    | exact superpose eq42443 eq8
    | exact resolve eq8 eq42443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42443
  have eq53039 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7441 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7441
    | (have j0 := eq7441 (σ X0)
       grind)
    | exact resolve eq7441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441
  have eq53180 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53039 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq53039
    | (have j0 := eq53039 X0
       grind)
    | exact resolve eq53039 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53039
  have eq70141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3531 X0 (M.op X0 X0)
       have i₂ := eq13215 X0
       grind)
    | exact superpose eq13215 eq3531
    | (have j0 := eq3531 X0 (M.op X0 X0)
       grind)
    | exact resolve eq3531 eq13215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq70182 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3531 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq3531
    | (have j0 := eq3531 (τ X0) (τ X1)
       grind)
    | exact resolve eq3531 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3531
  have eq70451 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq70182 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq70182
    | (have j0 := eq70182 X0 X1
       grind)
    | exact resolve eq70182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70182
  have eq70463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq70141 X0
       have j1 := eq3251 X0
       grind)
    | (have r₁ := eq70141 X0
       have r₂ := eq3251 X0
       grind)
    | exact resolve eq70141 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251 eq70141
  have eq70496 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq70451 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70451
    | (have j0 := eq70451 X0 X1
       grind)
    | exact resolve eq70451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70451
  have eq70516 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70496 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq70496
    | (have j0 := eq70496 X0 X1
       grind)
    | exact resolve eq70496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70496
  have eq70528 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70516 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70516
    | (have j0 := eq70516 X0 X1
       grind)
    | exact resolve eq70516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70516
  have eq71399 : y ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq70528 x y
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq70528
    | (have j0 := eq70528 x y
       grind)
    | exact resolve eq70528 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71403 : x ≠ (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq70528 y x
       have i₂ := eq18941
       grind)
    | exact superpose eq18941 eq70528
    | (have j0 := eq70528 y x
       grind)
    | exact resolve eq70528 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70528
  have eq71465 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq71403
       have r₂ := eq9001
       grind)
    | exact resolve eq71403 eq9001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001 eq71403
  have eq71466 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq71399
       have r₂ := eq19399
       grind)
    | exact resolve eq71399 eq19399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399 eq71399
  have eq72623 : (σ y) = (σ (M.op y x)) ∨ (k y y) = (M.op y x) := by
    first
    | (have i₁ := eq14843 y
       have i₂ := eq71465
       grind)
    | exact superpose eq71465 eq14843
    | exact resolve eq14843 eq71465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14843
  have eq72626 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
    first
    | (have i₁ := eq70463 y
       have i₂ := eq71465
       grind)
    | exact superpose eq71465 eq70463
    | exact resolve eq70463 eq71465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70463
  have eq84285 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq84359 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84285 X0 X1
       have j1 := eq156 X1 X0
       grind)
    | (have r₁ := eq84285 (k X1 X1) X0
       have r₂ := eq156 X0 X1
       grind)
    | (have r₁ := eq84285 X0 (σ (k X1 X1))
       have r₂ := eq156 (σ X0) X1
       grind)
    | (have r₁ := eq84285 X1 X0
       have r₂ := eq156 X0 X1
       grind)
    | exact resolve eq84285 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq84285
  have eq93113 : (M.op y x) = (τ (σ y)) ∨ (k y y) = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op y x)
       have i₂ := eq72623
       grind)
    | exact superpose eq72623 eq9
    | exact resolve eq9 eq72623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72623
  have eq93298 : (k y y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93113
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq93113
    | exact resolve eq93113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93113
  have eq102173 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq84359 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq84359 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq84359 eq17
    | (have j1 := eq84359 (τ X1) X0
       grind)
    | exact resolve eq17 eq84359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq84359
  have eq102598 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq102173 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq102173
    | (have j0 := eq102173 X0 X1
       grind)
    | exact resolve eq102173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102173
  have eq102689 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102598 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102598
    | (have j0 := eq102598 X0 X1
       grind)
    | exact resolve eq102598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102598
  have eq104764 : y = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18941
       have i₂ := eq102689 y x
       grind)
    | exact superpose eq102689 eq18941
    | (have j1 := eq102689 y x
       grind)
    | exact resolve eq18941 eq102689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18941 eq102689
  have eq106619 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq104764
       grind)
    | exact superpose eq104764 eq189
    | (have j0 := eq189 x
       grind)
    | exact resolve eq189 eq104764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106648 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14837 x
       have i₂ := eq104764
       grind)
    | exact superpose eq104764 eq14837
    | (have j0 := eq14837 x
       grind)
    | exact resolve eq14837 eq104764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104764
  have eq106691 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq106648
       have r₂ := eq43291
       grind)
    | exact resolve eq106648 eq43291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106648
  have eq106694 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq106619
       have r₂ := eq43291
       grind)
    | exact resolve eq106619 eq43291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43291 eq106619
  have eq113296 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3471
       have i₂ := eq106694
       grind)
    | exact superpose eq106694 eq3471
    | exact resolve eq3471 eq106694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471 eq106694
  have eq113458 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq113296
       have i₂ := eq71466
       grind)
    | exact superpose eq71466 eq113296
    | exact resolve eq113296 eq71466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113296
  have eq113469 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq113458
       have r₂ := eq106691
       grind)
    | exact resolve eq113458 eq106691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106691 eq113458
  have eq113474 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq113469
       have i₂ := eq8788
       grind)
    | exact superpose eq8788 eq113469
    | exact resolve eq113469 eq8788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8788 eq113469
  have eq119500 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq113474
       grind)
    | exact superpose eq113474 eq14
    | exact resolve eq14 eq113474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113474
  have eq119618 : x = (M.op y x) := by
    first
    | (have r₁ := eq119500
       have r₂ := eq9000
       grind)
    | exact resolve eq119500 eq9000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9000 eq119500
  have eq120187 : x ≠ x ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13124
       have i₂ := eq119618
       grind)
    | exact superpose eq119618 eq13124
    | (have r₁ := eq13124
       have r₂ := eq119618
       grind)
    | exact resolve eq13124 eq119618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq120198 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq72626
       have i₂ := eq119618
       grind)
    | exact superpose eq119618 eq72626
    | exact resolve eq72626 eq119618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72626
  have eq120237 : x = (M.op y y) := by grind
  clear eq120187
  have eq126160 : y = (k (τ (M.op (σ y) (σ x))) y) := by
    first
    | (have i₁ := eq58 y
       have i₂ := eq120198
       grind)
    | exact superpose eq120198 eq58
    | exact resolve eq58 eq120198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq126174 : (σ y) = (M.op (σ y) (σ x)) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq3198 y
       have i₂ := eq120198
       grind)
    | exact superpose eq120198 eq3198
    | (have j0 := eq3198 y
       grind)
    | exact resolve eq3198 eq120198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198
  have eq126345 : (k y y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq126174
       have i₂ := eq71465
       grind)
    | exact superpose eq71465 eq126174
    | exact resolve eq126174 eq71465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126174
  have eq126360 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq126345
       have i₂ := eq119618
       grind)
    | exact superpose eq119618 eq126345
    | exact resolve eq126345 eq119618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126345
  have eq142928 : y = (k (τ (σ y)) y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq126160
       have i₂ := eq126360
       grind)
    | exact superpose eq126360 eq126160
    | exact resolve eq126160 eq126360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126160 eq126360
  have eq143006 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq142928
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq142928
    | exact resolve eq142928 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142928
  have eq143282 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq93298
       have i₂ := eq143006
       grind)
    | exact superpose eq143006 eq93298
    | exact resolve eq93298 eq143006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93298
  have eq143329 : x ≠ y ∨ x = (k y y) := by grind
  clear eq143006
  have eq143343 : y = (M.op y x) ∨ x = (k y y) := by grind
  clear eq143282
  have eq143376 : x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq143343
       have i₂ := eq119618
       grind)
    | exact superpose eq119618 eq143343
    | exact resolve eq143343 eq119618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143343
  have eq143395 : x = (k y y) := by
    first
    | (have r₁ := eq143376
       have r₂ := eq143329
       grind)
    | exact resolve eq143376 eq143329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143329 eq143376
  have eq143606 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq143395
       grind)
    | exact superpose eq143395 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq143395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143693 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq143606
       have i₂ := eq120198
       grind)
    | exact superpose eq120198 eq143606
    | exact resolve eq143606 eq120198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143606
  have eq179905 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq120198
       have i₂ := eq53180 y
       grind)
    | exact superpose eq53180 eq120198
    | (have j1 := eq53180 y
       grind)
    | exact resolve eq120198 eq53180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53180 eq120198
  have eq179959 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq179905
       have i₂ := eq143395
       grind)
    | exact superpose eq143395 eq179905
    | exact resolve eq179905 eq143395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143395 eq179905
  have eq179975 : y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq179959
       have i₂ := eq71465
       grind)
    | exact superpose eq71465 eq179959
    | exact resolve eq179959 eq71465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71465 eq179959
  have eq179982 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq179975
       have i₂ := eq119618
       grind)
    | exact superpose eq119618 eq179975
    | exact resolve eq179975 eq119618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119618 eq179975
  have eq181420 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 (σ x) (σ y)
       have i₂ := eq179982
       grind)
    | exact superpose eq179982 eq8
    | exact resolve eq8 eq179982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179982
  have eq183848 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq181420
       grind)
    | exact superpose eq181420 eq14
    | exact resolve eq14 eq181420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181420
  have eq183884 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq183848
       have i₂ := eq71466
       grind)
    | exact superpose eq71466 eq183848
    | exact resolve eq183848 eq71466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71466 eq183848
  have eq185062 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq183884
       have i₂ := eq37816 x x
       grind)
    | exact superpose eq37816 eq183884
    | (have j1 := eq37816 x x
       grind)
    | exact resolve eq183884 eq37816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37816
  have eq185067 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq817 x x
       grind)
    | (have r₁ := eq185062
       have r₂ := eq817 x x
       grind)
    | exact resolve eq185062 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq185062
  have eq186806 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq185067
       grind)
    | exact superpose eq185067 eq189
    | (have j0 := eq189 x
       grind)
    | exact resolve eq189 eq185067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq186834 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq14837 x
       have i₂ := eq185067
       grind)
    | exact superpose eq185067 eq14837
    | (have j0 := eq14837 x
       grind)
    | exact resolve eq14837 eq185067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837 eq185067
  have eq186858 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq186834
  have eq186867 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq186806
  have eq198684 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq183884
       have i₂ := eq186867
       grind)
    | exact superpose eq186867 eq183884
    | exact resolve eq183884 eq186867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183884 eq186867
  have eq198801 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq198684
  have eq198846 : x = y := by
    first
    | (have r₁ := eq198801
       have r₂ := eq186858
       grind)
    | exact resolve eq198801 eq186858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186858 eq198801
  have eq200996 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq198846
       grind)
    | exact superpose eq198846 eq14
    | exact resolve eq14 eq198846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201073 : x = (M.op x x) := by
    first
    | (have i₁ := eq120237
       have i₂ := eq198846
       grind)
    | exact superpose eq198846 eq120237
    | exact resolve eq120237 eq198846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120237
  have eq201103 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq143693
       have i₂ := eq198846
       grind)
    | exact superpose eq198846 eq143693
    | exact resolve eq143693 eq198846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143693 eq198846
  have eq201113 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq201103
  have eq201142 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq200996
       have i₂ := eq201073
       grind)
    | exact superpose eq201073 eq200996
    | exact resolve eq200996 eq201073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200996 eq201073
  have eq201152 : False := by grind
  exact eq201152

/-- `Equation326`: `x ◇ y = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation326 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law326 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law326.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq86 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq131 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq117
    | exact resolve eq117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq162 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq30 X1 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq30 X0 X0 X2
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq30 X2 X1 X0
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq30 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (M.op X1 X1) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq81
    | (have j0 := eq81 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq81 (M.op X0 X0) X0
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq81 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq308 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq131 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq131
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq33 X0 X1
       grind)
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
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
  have eq370 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq131
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq131 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq391 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq394 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq988 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq391 (τ X0)
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq391
    | (have j0 := eq391 (τ X0)
       grind)
    | exact resolve eq391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq990 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq988 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq988
    | (have j0 := eq988 X0
       grind)
    | exact resolve eq988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq993 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq990
    | (have j0 := eq990 X0
       grind)
    | exact resolve eq990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1103 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1132 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq993 (τ X0)
       have i₂ := eq66 X0 X0
       grind)
    | exact superpose eq66 eq993
    | (have j0 := eq993 (τ X0)
       grind)
    | exact resolve eq993 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1232 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1255 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq1103 X0 (τ X1)
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq1103 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq1103 eq26
    | (have j1 := eq1103 X0 (τ X1)
       grind)
    | exact resolve eq26 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1260 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1255 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq1255
    | (have j0 := eq1255 X0 X1
       grind)
    | exact resolve eq1255 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq2083 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2088 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2852 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2927 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2852 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2852
    | (have j0 := eq2852 X0 X1
       grind)
    | exact resolve eq2852 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq3149 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq2927 X0 X0
       grind)
    | exact superpose eq2927 eq391
    | (have j0 := eq391 X0
       have j1 := eq2927 X0 X0
       grind)
    | (have r₁ := eq391 x
       have r₂ := eq2927 x x
       grind)
    | exact resolve eq391 eq2927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq3176 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq6011 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308
    | (have j0 := eq308 X1 (τ X0)
       grind)
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq6111 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6011 X0 X1
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq6011
    | (have j0 := eq6011 X0 X1
       grind)
    | exact resolve eq6011 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq6011
  have eq6457 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq6458 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457
  have eq6727 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq176 x y X0
       grind)
    | exact superpose eq176 eq14
    | (have j1 := eq176 x y X0
       grind)
    | exact resolve eq14 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq7565 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
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
  have eq7574 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq394 X0 X0
       grind)
    | exact superpose eq394 eq8
    | (have j1 := eq394 X0 X0
       grind)
    | exact resolve eq8 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq7632 : y = (k y x) := by
    first
    | (have j1 := eq1232 x y
       grind)
    | (have r₁ := eq7565
       have r₂ := eq1232 x y
       grind)
    | exact resolve eq7565 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565
  have eq7855 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1103 x y
       have i₂ := eq7632
       grind)
    | exact superpose eq7632 eq1103
    | (have j0 := eq1103 x y
       grind)
    | exact resolve eq1103 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14341 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq342 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq342 X0 X1
       grind)
    | exact superpose eq342 eq9
    | (have j1 := eq342 X0 X1
       grind)
    | exact resolve eq9 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq14399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14341 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14341
    | (have j0 := eq14341 X0 X1
       grind)
    | exact resolve eq14341 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq14510 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1132 X0
       have i₂ := eq6111 X0 X0
       grind)
    | exact superpose eq6111 eq1132
    | (have j0 := eq1132 X0
       have j1 := eq6111 X0 X0
       grind)
    | (have r₁ := eq1132 x
       have r₂ := eq6111 x x
       grind)
    | exact resolve eq1132 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq6111
  have eq14518 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14510
  have eq19244 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14518 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14518
    | (have j0 := eq14518 (σ X0)
       grind)
    | exact resolve eq14518 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14518
  have eq19385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19244 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq19244
    | (have j0 := eq19244 X0
       grind)
    | exact resolve eq19244 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19244
  have eq28837 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1 X1
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq187 X0 X1
       have i₂ := eq1103 (M.op X0 X1) X1
       grind)
    | exact superpose eq1103 eq187
    | (have j1 := eq1103 X0 X1
       grind)
    | (have r₁ := eq187 X1 X1
       have r₂ := eq1103 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq1103 (M.op X0 X1) X1
       grind)
    | exact resolve eq187 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28839 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq187 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq187
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28991 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq187 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq29005 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28839
  have eq29007 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28837 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28837
  have eq30422 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq28991 (σ X0)
       grind)
    | exact superpose eq28991 eq25
    | exact resolve eq25 eq28991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28991
  have eq31650 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq29005 (τ X0) X1
       grind)
    | exact superpose eq29005 eq19
    | (have j1 := eq29005 (τ X0) X1
       grind)
    | exact resolve eq19 eq29005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31754 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31650 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31650
    | (have j0 := eq31650 X0 X1
       grind)
    | exact resolve eq31650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31650
  have eq39660 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1069 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1069
    | (have j0 := eq1069 X1 (σ X0)
       grind)
    | exact resolve eq1069 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40015 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1069 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq40016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40015 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40015
    | (have j0 := eq40015 X0
       grind)
    | exact resolve eq40015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40015
  have eq40066 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39660 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq39660
    | (have j0 := eq39660 X0 X1
       grind)
    | exact resolve eq39660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39660
  have eq40142 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40016 X0
       have i₂ := eq29005 X0 X0
       grind)
    | exact superpose eq29005 eq40016
    | (have j0 := eq40016 X0
       have j1 := eq29005 X0 X0
       grind)
    | (have r₁ := eq40016 x
       have r₂ := eq29005 x x
       grind)
    | exact resolve eq40016 eq29005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29005
  have eq40182 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq40142 X0
       have j1 := eq40016 X0
       grind)
    | (have r₁ := eq40142 X0
       have r₂ := eq40016 X0
       grind)
    | exact resolve eq40142 eq40016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016 eq40142
  have eq40208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2083
       have i₂ := eq6458 y x
       grind)
    | exact superpose eq6458 eq2083
    | (have j1 := eq6458 y x
       grind)
    | exact resolve eq2083 eq6458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq40219 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq40208
  have eq40685 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40182 (σ X0)
       have i₂ := eq3176 X0
       grind)
    | exact superpose eq3176 eq40182
    | (have j0 := eq40182 (σ X0)
       have j1 := eq3176 X0
       grind)
    | (have r₁ := eq40182 (σ X0)
       have r₂ := eq3176 X0
       grind)
    | exact resolve eq40182 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176 eq40182
  have eq40699 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq40685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40685
  have eq40708 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40699 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40699
    | (have j0 := eq40699 X0
       grind)
    | exact resolve eq40699 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40699
  have eq42234 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40708 X1
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq40708 X0
       have i₂ := eq1103 (M.op X0 X0) X1
       grind)
    | exact superpose eq1103 eq40708
    | (have j1 := eq1103 X0 X1
       grind)
    | exact resolve eq40708 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40708
  have eq46719 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30422 X0
       have i₂ := eq370 X0 X1
       grind)
    | (have i₁ := eq30422 X0
       have i₂ := eq370 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq370 eq30422
    | (have j1 := eq370 X1 X0
       grind)
    | exact resolve eq30422 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq30422
  have eq50798 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq31754 (σ X0) X1
       grind)
    | exact superpose eq31754 eq13
    | (have j1 := eq31754 (σ X0) X1
       grind)
    | exact resolve eq13 eq31754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31754
  have eq50975 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50798 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50798
    | (have j0 := eq50798 X0 X1
       grind)
    | exact resolve eq50798 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50798
  have eq54744 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46719 x y
       grind)
    | exact superpose eq46719 eq14
    | (have j1 := eq46719 x y
       grind)
    | exact resolve eq14 eq46719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46719
  have eq54903 : x = (k x y) := by
    first
    | (have j1 := eq29007 x y
       grind)
    | (have r₁ := eq54744
       have r₂ := eq29007 x y
       grind)
    | exact resolve eq54744 eq29007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29007 eq54744
  have eq55199 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq30 y X0 x
       have i₂ := eq54903
       grind)
    | exact superpose eq54903 eq30
    | (have j0 := eq30 y X0 x
       grind)
    | exact resolve eq30 eq54903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq56848 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6727 X0
       have i₂ := eq6458 y x
       grind)
    | exact superpose eq6458 eq6727
    | (have j0 := eq6727 X0
       have j1 := eq6458 y x
       grind)
    | exact resolve eq6727 eq6458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727
  have eq56860 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq56848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56848
  have eq57386 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56860 (σ x)
       grind)
    | exact superpose eq56860 eq14
    | exact resolve eq14 eq56860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56860
  have eq59627 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1260 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1260
    | (have j0 := eq1260 X1 (σ X0)
       grind)
    | exact resolve eq1260 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq59687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59627 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59627
    | (have j0 := eq59627 X0 X1
       grind)
    | exact resolve eq59627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59627
  have eq59698 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59687 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59687
    | (have j0 := eq59687 X0 X1
       grind)
    | exact resolve eq59687 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59687
  have eq61306 : (σ x) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40066 y x
       have i₂ := eq54903
       grind)
    | exact superpose eq54903 eq40066
    | (have j0 := eq40066 y x
       grind)
    | exact resolve eq40066 eq54903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54903
  have eq61504 : (M.op y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 (M.op y x)
       have i₂ := eq61306
       grind)
    | exact superpose eq61306 eq9
    | exact resolve eq9 eq61306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61306
  have eq61541 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq61504
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq61504
    | exact resolve eq61504 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61504
  have eq63481 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14399 x y
       grind)
    | exact superpose eq14399 eq14
    | (have j1 := eq14399 x y
       grind)
    | exact resolve eq14 eq14399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14399
  have eq63490 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq42234 x y
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 x y
       grind)
    | exact resolve eq63481 eq42234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42234 eq63481
  have eq63615 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50975 y y
       have i₂ := eq63490
       grind)
    | exact superpose eq63490 eq50975
    | exact resolve eq50975 eq63490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50975 eq63490
  have eq63619 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq63615
  have eq63634 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55199 y
       have i₂ := eq63619
       grind)
    | exact superpose eq63619 eq55199
    | exact resolve eq55199 eq63619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55199 eq63619
  have eq63747 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq63634
  have eq65335 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq59698 X0 X0
       grind)
    | exact superpose eq59698 eq391
    | (have j0 := eq391 X0
       have j1 := eq59698 X0 X0
       grind)
    | (have r₁ := eq391 x
       have r₂ := eq59698 x x
       grind)
    | exact resolve eq391 eq59698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59698
  have eq65362 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq65335 X0
       have j1 := eq391 X0
       grind)
    | (have r₁ := eq65335 X0
       have r₂ := eq391 X0
       grind)
    | exact resolve eq65335 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq65335
  have eq65741 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65362 x
       have i₂ := eq61541
       grind)
    | exact superpose eq61541 eq65362
    | (have j0 := eq65362 x
       grind)
    | exact resolve eq65362 eq61541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61541
  have eq65747 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq65741
       have r₂ := eq63747
       grind)
    | exact resolve eq65741 eq63747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65741
  have eq65774 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq57386
       have i₂ := eq65747
       grind)
    | exact superpose eq65747 eq57386
    | exact resolve eq57386 eq65747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57386 eq65747
  have eq65882 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by grind
  clear eq65774
  have eq66333 : (σ x) ≠ (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65882
       have i₂ := eq40219
       grind)
    | exact superpose eq40219 eq65882
    | exact resolve eq65882 eq40219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40219 eq65882
  have eq66337 : (σ x) ≠ (σ y) ∨ x = (M.op y x) := by grind
  clear eq66333
  have eq66340 : x = (M.op y x) := by
    first
    | (have r₁ := eq66337
       have r₂ := eq63747
       grind)
    | exact resolve eq66337 eq63747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63747 eq66337
  have eq68789 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2088 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq68790 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68789 X0 X1
       have j1 := eq343 X1 X0
       grind)
    | (have r₁ := eq68789 (k X1 X1) X0
       have r₂ := eq343 X0 X1
       grind)
    | (have r₁ := eq68789 X0 (σ (k X1 X1))
       have r₂ := eq343 (σ X0) X1
       grind)
    | (have r₁ := eq68789 X1 X0
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq68789 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq68789
  have eq68847 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq68790 (τ X1) X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq68790 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq68790 eq19
    | (have j1 := eq68790 (τ X1) X0
       grind)
    | exact resolve eq19 eq68790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq68848 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq68790 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq68790 X0 (σ X0)
       grind)
    | exact superpose eq68790 eq9
    | (have j1 := eq68790 X1 X0
       grind)
    | exact resolve eq9 eq68790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68790
  have eq68888 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq68847 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq68847
    | (have j0 := eq68847 X0 X1
       grind)
    | exact resolve eq68847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68847
  have eq68897 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68888 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68888
    | (have j0 := eq68888 X0 X1
       grind)
    | exact resolve eq68888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68888
  have eq69770 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq68848 (σ X0) X1
       grind)
    | exact superpose eq68848 eq13
    | (have j1 := eq68848 (σ X0) X1
       grind)
    | exact resolve eq13 eq68848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68848
  have eq69795 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69770 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69770
    | (have j0 := eq69770 X0 X1
       grind)
    | exact resolve eq69770 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69770
  have eq71132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69795 x y
       grind)
    | exact superpose eq69795 eq14
    | (have j1 := eq69795 x y
       grind)
    | exact resolve eq14 eq69795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71224 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq71132
       have i₂ := eq7632
       grind)
    | exact superpose eq7632 eq71132
    | exact resolve eq71132 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7632 eq71132
  have eq71277 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71224
       have i₂ := eq7855
       grind)
    | exact superpose eq7855 eq71224
    | (have r₁ := eq71224
       have r₂ := eq7855
       grind)
    | exact resolve eq71224 eq7855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7855 eq71224
  have eq71280 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71277
  have eq71428 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6458 y y
       have i₂ := eq71280
       grind)
    | exact superpose eq71280 eq6458
    | (have j0 := eq6458 y y
       grind)
    | exact resolve eq6458 eq71280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq71449 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68897 y y
       have i₂ := eq71280
       grind)
    | exact superpose eq71280 eq68897
    | exact resolve eq68897 eq71280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68897 eq71280
  have eq71454 : x = (M.op y y) ∨ x = y := by grind
  clear eq71449
  have eq71465 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq71428
  have eq72053 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq71465
  have eq72078 : x = (M.op y y) := by
    first
    | (have r₁ := eq72053
       have r₂ := eq71454
       grind)
    | exact resolve eq72053 eq71454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71454 eq72053
  have eq72100 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq72078
       grind)
    | exact superpose eq72078 eq8
    | exact resolve eq8 eq72078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72214 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq65362 y
       have i₂ := eq72078
       grind)
    | exact superpose eq72078 eq65362
    | (have j0 := eq65362 y
       grind)
    | exact resolve eq65362 eq72078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72706 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq72100 (τ X0)
       grind)
    | exact superpose eq72100 eq38
    | (have j0 := eq38 X0 y
       grind)
    | exact resolve eq38 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq72793 : ∀ X0 : G, (τ X0) = (M.op y x) ∨ (k (σ y) X0) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq72706 X0
       have i₂ := eq72100 y
       grind)
    | exact superpose eq72100 eq72706
    | (have j0 := eq72706 X0
       grind)
    | exact resolve eq72706 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72706
  have eq73113 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq72793 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq72793
    | (have j0 := eq72793 X0
       grind)
    | exact resolve eq72793 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72793
  have eq84946 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq73113 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73113
    | exact resolve eq73113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73113
  have eq84998 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq84946 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq84946
    | (have j0 := eq84946 X0
       grind)
    | exact resolve eq84946 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84946
  have eq85127 : ∀ X0 : G, (k y X0) = (τ (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k y X0)
       have i₂ := eq84998 X0
       grind)
    | exact superpose eq84998 eq9
    | (have j1 := eq84998 X0
       grind)
    | exact resolve eq9 eq84998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84998
  have eq85170 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq85127 X0
       have i₂ := eq9 (M.op X0 x)
       grind)
    | exact superpose eq9 eq85127
    | (have j0 := eq85127 X0
       grind)
    | exact resolve eq85127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85127
  have eq85361 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7574 y x
       have i₂ := eq85170 y
       grind)
    | exact superpose eq85170 eq7574
    | (have j1 := eq85170 y
       grind)
    | exact resolve eq7574 eq85170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574 eq85170
  have eq85546 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq85361 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq85361
    | exact resolve eq85361 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85361
  have eq85597 : ∀ X0 : G, x = y ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq85546 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq85546
    | (have j0 := eq85546 X0
       grind)
    | exact resolve eq85546 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66340 eq85546
  have eq85598 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq85597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85597
  have eq85949 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq85598 (σ x)
       grind)
    | exact superpose eq85598 eq14
    | exact resolve eq14 eq85598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85598
  have eq85971 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq85949
       have i₂ := eq72100 x
       grind)
    | exact superpose eq72100 eq85949
    | exact resolve eq85949 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72100 eq85949
  have eq86681 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq85971
       have i₂ := eq69795 x x
       grind)
    | exact superpose eq69795 eq85971
    | (have j1 := eq69795 x x
       grind)
    | exact resolve eq85971 eq69795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69795
  have eq86684 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85971
       have i₂ := eq19385 x
       grind)
    | exact superpose eq19385 eq85971
    | (have j1 := eq19385 x
       grind)
    | exact resolve eq85971 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19385
  have eq86696 : x = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq1103 x x
       grind)
    | (have r₁ := eq86684
       have r₂ := eq1103 x x
       grind)
    | exact resolve eq86684 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq86684
  have eq86698 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq1232 x x
       grind)
    | (have r₁ := eq86681
       have r₂ := eq1232 x x
       grind)
    | exact resolve eq86681 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq86681
  have eq86847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq65362 x
       have i₂ := eq86696
       grind)
    | exact superpose eq86696 eq65362
    | (have j0 := eq65362 x
       grind)
    | exact resolve eq65362 eq86696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65362 eq86696
  have eq86916 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq86847
  have eq87063 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq40066 x x
       have i₂ := eq86698
       grind)
    | exact superpose eq86698 eq40066
    | (have j0 := eq40066 x x
       grind)
    | exact resolve eq40066 eq86698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40066 eq86698
  have eq87068 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq87063
  have eq88228 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq85971
       have i₂ := eq86916
       grind)
    | exact superpose eq86916 eq85971
    | exact resolve eq85971 eq86916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85971 eq86916
  have eq88392 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq88228
  have eq88445 : x = y := by
    first
    | (have r₁ := eq88392
       have r₂ := eq87068
       grind)
    | exact resolve eq88392 eq87068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87068 eq88392
  have eq88467 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq14
    | exact resolve eq14 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88542 : x = (M.op x x) := by
    first
    | (have i₁ := eq72078
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq72078
    | exact resolve eq72078 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72078
  have eq88561 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72214
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq72214
    | exact resolve eq72214 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72214 eq88445
  have eq88590 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq88561
  have eq88624 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88467
       have i₂ := eq88542
       grind)
    | exact superpose eq88542 eq88467
    | exact resolve eq88467 eq88542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88467 eq88542
  have eq88627 : False := by grind
  exact eq88627
