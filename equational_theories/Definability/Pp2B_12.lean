import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq10
    | exact resolve eq10 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq122 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq99
    | exact resolve eq99 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq123 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq122
    | exact resolve eq122 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
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
  have eq136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq133
       have i₂ := eq109 sF1
       grind)
    | exact superpose eq109 eq133
    | exact resolve eq133 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq109 sF0
       grind)
    | exact superpose eq109 eq136
    | exact resolve eq136 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq430 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq51 X2 X3 X0
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq581 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq430 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq430 (M.op X0 X0) X1
       grind)
    | exact superpose eq430 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq430 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq430 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq582 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq581 X0 x X2
       grind)
    | (have r₁ := eq581 X0 x X2
       have r₂ := eq430 X0 x
       grind)
    | (have r₁ := eq581 x X0 X2
       have r₂ := eq430 X0 x
       grind)
    | exact resolve eq581 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq633 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq74 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq654 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq655 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq654 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq660 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq5826 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq432 X1 x X2 x
       have i₂ := eq511 X1 x X2 x X0
       grind)
    | exact superpose eq511 eq432
    | exact resolve eq432 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq6342 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5826 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq432 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq432 eq5826
    | exact resolve eq5826 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq5826
  have eq17340 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq660 X0 X1
       have j1 := eq651 X1 X0
       grind)
    | (have r₁ := eq660 X1 X0
       have r₂ := eq651 X0 X1
       grind)
    | (have r₁ := eq660 X1 X1
       have r₂ := eq651 X1 X1
       grind)
    | exact resolve eq660 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq660
  have eq17450 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17340 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq17340
    | exact resolve eq17340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17525 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17340 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17340
    | (have j0 := eq17340 y X0
       grind)
    | exact resolve eq17340 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17340
  have eq17805 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17450 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq17450
    | (have j0 := eq17450 X0 X1
       grind)
    | exact resolve eq17450 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq17450
  have eq21648 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq47
    | exact resolve eq47 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq21649 : ∀ X0 : G, (σ (k X0 (k x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21648 X0
       have i₂ := eq582 sF2 (σ X0)
       grind)
    | exact superpose eq582 eq21648
    | exact resolve eq21648 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq21650 : ∀ X0 : G, (σ (k X0 (M.op x x))) = (M.op (M.op (σ x) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21649 X0
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq21649
    | exact resolve eq21649 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq21649
  have eq21651 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ X0)) = (σ (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq21650 X0
       have i₂ := eq582 x X0
       grind)
    | exact superpose eq582 eq21650
    | exact resolve eq21650 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq21650
  have eq27178 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op x x) X0)) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq21651 eq14
    | exact resolve eq14 eq21651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21651
  have eq34362 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27178 (M.op x (M.op X0 X0)) X1
       have i₂ := eq6342 x X0 x
       grind)
    | exact superpose eq6342 eq27178
    | exact resolve eq27178 eq6342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6342 eq27178
  have eq34596 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op x (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34362 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34362
    | (have j0 := eq34362 X0 X1
       grind)
    | exact resolve eq34362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34362
  have eq37512 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17525 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17525
    | (have j0 := eq17525 x
       grind)
    | exact resolve eq17525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17525
  have eq37551 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq37512
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq37512
    | exact resolve eq37512 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37512
  have eq37587 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq37551
    | exact resolve eq37551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37551
  have eq37998 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17805 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq17805
    | (have j0 := eq17805 X1 X1
       grind)
    | exact resolve eq17805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq38544 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq37998 x y
       grind)
    | exact superpose eq37998 eq44
    | (have j1 := eq37998 x y
       grind)
    | exact resolve eq44 eq37998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq37998
  have eq38750 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38544
    | exact resolve eq38544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38544
  have eq38801 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq38750
    | exact resolve eq38750 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38750
  have eq38837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38801 eq37587
    | exact resolve eq37587 eq38801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37587 eq38801
  have eq38844 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq38837
       have r₂ := eq27
       grind)
    | exact resolve eq38837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38837
  have eq39026 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38844 eq123
    | exact resolve eq123 eq38844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq38844
  have eq39234 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq39026
    | exact resolve eq39026 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39026
  have eq39235 : y = (M.op y y) := by grind
  clear eq39234
  have eq39239 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39235
       have i₂ := eq430 X0 y
       grind)
    | (have i₁ := eq39235
       have i₂ := eq430 y X0
       grind)
    | exact superpose eq430 eq39235
    | exact resolve eq39235 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq39235
  have eq39710 : ∀ X0 : G, (σ (M.op x (M.op X0 X0))) = (M.op (σ x) y) := by
    intro X0
    first
    | (have i₁ := eq34596 X0 (σ (M.op x (M.op X0 X0)))
       have i₂ := eq39239 (σ (M.op x (M.op X0 X0)))
       grind)
    | exact superpose eq39239 eq34596
    | exact resolve eq34596 eq39239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34596
  have eq39818 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq39239 sF0
       grind)
    | exact superpose eq39239 eq139
    | exact resolve eq139 eq39239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq39908 : y = (σ y) := by
    first
    | (have i₁ := eq39818
       have i₂ := eq39239 sF1
       grind)
    | exact superpose eq39239 eq39818
    | exact resolve eq39818 eq39239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39818
  have eq39985 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq39710 x
       have i₂ := eq39239 x
       grind)
    | exact superpose eq39239 eq39710
    | exact resolve eq39710 eq39239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39239 eq39710
  have eq40178 : y = (σ y) := by
    first
    | (have i₁ := eq39908
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39908
    | exact resolve eq39908 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39908
  have eq40219 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq39985
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39985
    | exact resolve eq39985 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39985
  have eq40342 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq20 eq40219
    | exact resolve eq40219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40219
  have eq40410 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq40178 eq26
    | exact resolve eq26 eq40178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40178
  have eq43325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40342 eq40410
    | exact resolve eq40410 eq40342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40342 eq40410
  have eq43326 : False := by grind
  exact eq43326

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq50
    | exact resolve eq50 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq77
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq89 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq75 sF3
       grind)
    | exact superpose eq75 eq73
    | exact resolve eq73 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq90 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq89
    | exact resolve eq89 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq134 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq75 sF1
       grind)
    | exact superpose eq75 eq131
    | exact resolve eq131 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq134
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq134
    | exact resolve eq134 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq330 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq14
    | exact resolve eq14 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq563 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X1 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq556
    | exact resolve eq556 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq556 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq65 X0 (M.op X0 X0) X2
       have i₂ := eq556 (M.op X0 X0) X1
       grind)
    | exact superpose eq556 eq65
    | (have r₁ := eq65 X1 (M.op X1 X1) X2
       have r₂ := eq556 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq65 X0 (M.op X0 X0) X2
       have r₂ := eq556 X0 (M.op X0 X0)
       grind)
    | exact resolve eq65 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq814 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq813 X0 x X2
       grind)
    | (have r₁ := eq813 X0 x X2
       have r₂ := eq556 X0 x
       grind)
    | (have r₁ := eq813 x X0 X2
       have r₂ := eq556 X0 x
       grind)
    | exact resolve eq813 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq813
  have eq1601 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X1 X1)) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X1 (σ X0) (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq476
    | exact resolve eq476 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4057 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 (σ X0) X0 X1
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq330
    | exact resolve eq330 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq4064 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k X1 (k (τ (σ X0)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4057 X0 X1
       have i₂ := eq814 (σ X0) (σ X1)
       grind)
    | exact superpose eq814 eq4057
    | exact resolve eq4057 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4106 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4064 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4064
    | exact resolve eq4064 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064
  have eq4125 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (M.op (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4106 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq4106
    | exact resolve eq4106 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4106
  have eq4129 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4125 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq4125
    | exact resolve eq4125 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq4125
  have eq4131 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4129 X0 X1
       have i₂ := eq814 X0 X1
       grind)
    | exact superpose eq814 eq4129
    | exact resolve eq4129 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq4129
  have eq25486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq25487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq25486
    | exact resolve eq25486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25486
  have eq25495 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq25487
       have r₂ := eq28
       grind)
    | exact resolve eq25487 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25487
  have eq25500 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq25495 eq115
    | exact resolve eq115 eq25495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq25495
  have eq25630 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq25500
    | exact resolve eq25500 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25500
  have eq25631 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25630
  have eq25645 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq25631
       grind)
    | exact superpose eq25631 eq53
    | exact resolve eq53 eq25631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq25666 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq563 y X0
       have i₂ := eq25631
       grind)
    | exact superpose eq25631 eq563
    | exact resolve eq563 eq25631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq25631
  have eq25795 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25666 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25666
    | (have j0 := eq25666 X0
       grind)
    | exact resolve eq25666 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25666
  have eq87251 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X1 X1) X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1601 X0 X1
       have i₂ := eq4131 X1 X0
       grind)
    | exact superpose eq4131 eq1601
    | exact resolve eq1601 eq4131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq4131
  have eq88913 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25645 eq87251
    | exact resolve eq87251 eq25645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645 eq87251
  have eq88952 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq136 eq88913
    | exact resolve eq88913 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq88913
  have eq88954 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88952
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq88952
    | exact resolve eq88952 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88952
  have eq88955 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq88954
    | exact resolve eq88954 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88954
  have eq98402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88955
       have i₂ := eq25795 sF1
       grind)
    | exact superpose eq25795 eq88955
    | exact resolve eq88955 eq25795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25795 eq88955
  have eq98449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq98402
  have eq98462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq98449
    | exact resolve eq98449 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98449
  have eq98464 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq98462
       have r₂ := eq28
       grind)
    | exact resolve eq98462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98462
  have eq98467 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq98464 eq30
    | exact resolve eq30 eq98464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq98464
  have eq98837 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq98467
    | exact resolve eq98467 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq98467
  have eq98838 : x = y := by grind
  clear eq98837
  have eq98853 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq98838
       grind)
    | exact superpose eq98838 eq19
    | exact resolve eq19 eq98838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq98854 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq98838
       grind)
    | exact superpose eq98838 eq25
    | exact resolve eq25 eq98838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq98838
  have eq98993 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq98854
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq98854
    | exact resolve eq98854 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq98854
  have eq99021 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98993 eq27
    | exact resolve eq27 eq98993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq98993
  have eq99660 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq99021 eq80
    | exact resolve eq80 eq99021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq99021
  have eq99922 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq99660
       have i₂ := eq98853
       grind)
    | exact superpose eq98853 eq99660
    | exact resolve eq99660 eq98853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98853 eq99660
  have eq99927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99922 eq15
    | exact resolve eq15 eq99922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99922
  have eq100022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq99927
    | exact resolve eq99927 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq99927
  have eq100045 : False := by grind
  exact eq100045

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq530 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (σ X0) X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq76
  have eq690 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq685 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq685
    | exact resolve eq685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq740 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq690
  have eq4540 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (σ (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq535 (σ (M.op X2 X2)) X1 X0 (σ (M.op X2 X2))
       have i₂ := eq530 X2 (σ (M.op X2 X2)) X0
       grind)
    | exact superpose eq530 eq535
    | exact resolve eq535 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq535
  have eq21079 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op (M.op X1 X1) X0) (σ (M.op (τ X0) (τ X0)))) ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X2) X1 X0
       have i₂ := eq740 X0 X2
       grind)
    | exact superpose eq740 eq14
    | (have j1 := eq740 X0 X2
       grind)
    | exact resolve eq14 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq21161 : ∀ X0 X2 : G, (σ X2) = X0 ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq21079 X0 x X2
       have i₂ := eq4540 X0 x (τ X0)
       grind)
    | exact superpose eq4540 eq21079
    | (have j0 := eq21079 X0 x X2
       grind)
    | exact resolve eq21079 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4540 eq21079
  have eq21162 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq21161 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21161
  have eq43973 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21162 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21162
    | exact resolve eq21162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21162
  have eq44355 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq43973 y x
       grind)
    | exact superpose eq43973 eq49
    | (have j1 := eq43973 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq43973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq44547 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44355
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44355
    | exact resolve eq44355 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44355
  have eq44556 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq44547
    | exact resolve eq44547 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44547
  have eq44570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44556 eq43973
    | (have j0 := eq43973 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq43973 eq44556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43973 eq44556
  have eq44577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq44570
    | exact resolve eq44570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44570
  have eq44590 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44577
       have r₂ := eq28
       grind)
    | exact resolve eq44577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44577
  have eq44596 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq44590 eq30
    | exact resolve eq30 eq44590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44590
  have eq44728 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq44596
    | exact resolve eq44596 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44596
  have eq44729 : x = y := by grind
  clear eq44728
  have eq44748 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq44729
       grind)
    | exact superpose eq44729 eq19
    | exact resolve eq19 eq44729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq44749 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq44729
       grind)
    | exact superpose eq44729 eq25
    | exact resolve eq25 eq44729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq44729
  have eq44879 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44749
    | exact resolve eq44749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44749
  have eq44898 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44879 eq27
    | exact resolve eq27 eq44879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44879
  have eq45395 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq44898 eq69
    | exact resolve eq69 eq44898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq44898
  have eq45636 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq45395
       have i₂ := eq44748
       grind)
    | exact superpose eq44748 eq45395
    | exact resolve eq45395 eq44748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44748 eq45395
  have eq45650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45636 eq15
    | exact resolve eq15 eq45636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45636
  have eq45724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq45650
    | exact resolve eq45650 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq45650
  have eq45745 : False := by grind
  exact eq45745

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq124 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq124 (σ X1) (σ X0)
       grind)
    | exact superpose eq124 eq15
    | (have j1 := eq124 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq124 X1 X0
       grind)
    | exact superpose eq124 eq133
    | (have j0 := eq133 X0 X1
       have j1 := eq124 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq133 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq133
  have eq346 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq2195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq2210 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2195
  have eq6525 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2210
       grind)
    | exact superpose eq2210 eq10
    | exact resolve eq10 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq6538 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6525
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6525
    | exact resolve eq6525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525
  have eq6539 : x = y := by grind
  clear eq6538
  have eq16313 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6539
       grind)
    | exact superpose eq6539 eq16
    | exact resolve eq16 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539
  have eq16314 : False := by grind
  exact eq16314

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq99 (σ X1) (σ X0)
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq99 X1 X0
       grind)
    | exact superpose eq99 eq108
    | (have j0 := eq108 X0 X1
       have j1 := eq99 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq108 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq108
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq94 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq94 (σ X1) X0
       grind)
    | exact superpose eq94 eq22
    | exact resolve eq22 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq144 x y
       grind)
    | exact superpose eq144 eq16
    | (have j1 := eq144 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq144 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17798 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17799 : False := by grind
  exact eq17799

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq532 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (σ X0) X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq723 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq70
  have eq750 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq723
    | exact resolve eq723 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq777 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq750 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq750
    | (have j0 := eq750 X0 X1
       grind)
    | exact resolve eq750 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq750
  have eq4380 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (σ (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 (σ (M.op X2 X2)) X1 X0 (σ (M.op X2 X2))
       have i₂ := eq532 X2 (σ (M.op X2 X2)) X0
       grind)
    | exact superpose eq532 eq538
    | exact resolve eq538 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq538
  have eq21058 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (σ X2)) (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (σ X2)
       have i₂ := eq777 X0 X2
       grind)
    | exact superpose eq777 eq14
    | (have j1 := eq777 X0 X2
       grind)
    | exact resolve eq14 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq21168 : ∀ X0 X2 : G, (σ X2) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq21058 X0 x X2
       have i₂ := eq4380 (σ X2) x (τ X0)
       grind)
    | exact superpose eq4380 eq21058
    | (have j0 := eq21058 X0 x X2
       grind)
    | exact resolve eq21058 eq4380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4380 eq21058
  have eq21169 : ∀ X0 X2 : G, (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq21168 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21168
  have eq42936 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21169 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21169
    | exact resolve eq21169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21169
  have eq43316 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq42936 x y
       grind)
    | exact superpose eq42936 eq49
    | (have j1 := eq42936 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq42936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq43508 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq43316
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43316
    | exact resolve eq43316 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43316
  have eq43517 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq43508
    | exact resolve eq43508 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43508
  have eq43531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43517 eq42936
    | (have j0 := eq42936 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq42936 eq43517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42936 eq43517
  have eq43537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq43531
    | exact resolve eq43531 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43531
  have eq43550 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq43537
       have r₂ := eq28
       grind)
    | exact resolve eq43537 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43537
  have eq43556 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq43550 eq30
    | exact resolve eq30 eq43550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq43550
  have eq43687 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq43556
    | exact resolve eq43556 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43556
  have eq43688 : x = y := by grind
  clear eq43687
  have eq43708 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq43688
       grind)
    | exact superpose eq43688 eq19
    | exact resolve eq19 eq43688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq43709 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq43688
       grind)
    | exact superpose eq43688 eq25
    | exact resolve eq25 eq43688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq43688
  have eq43838 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43709
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43709
    | exact resolve eq43709 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43709
  have eq43857 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43838 eq27
    | exact resolve eq27 eq43838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43838
  have eq44350 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43857 eq69
    | exact resolve eq69 eq43857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq43857
  have eq44589 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq44350
       have i₂ := eq43708
       grind)
    | exact superpose eq43708 eq44350
    | exact resolve eq44350 eq43708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43708 eq44350
  have eq44604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44589 eq15
    | exact resolve eq15 eq44589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44589
  have eq44678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq44604
    | exact resolve eq44604 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44604
  have eq44699 : False := by grind
  exact eq44699

/-- `Equation215`: `x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation215 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law215 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law215.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
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
  have eq34 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 (M.op sF0 x))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq34
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq43 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq44 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 y
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq125 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq221 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq38 eq14
    | exact resolve eq14 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq355 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36
    | (have j0 := eq36 y x X0 X1
       grind)
    | exact resolve eq36 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq36
    | (have j0 := eq36 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq461 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq355 (M.op X0 (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq355
    | exact resolve eq355 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq629 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq357 (M.op X0 (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq357
    | exact resolve eq357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq12393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq12402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12393
    | exact resolve eq12393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq12411 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12402
       have r₂ := eq27
       grind)
    | exact resolve eq12402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12402
  have eq12413 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12411
    | exact resolve eq12411 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12411
  have eq12419 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12413 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12413
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12413
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12413
       grind)
    | exact resolve eq13 eq12413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12445 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12419
  have eq12634 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12445 eq107
    | exact resolve eq107 eq12445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq12445
  have eq12660 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq12634
    | exact resolve eq12634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12634
  have eq12663 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq12660
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq12660
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq12660
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12660
  have eq12672 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12663
       grind)
    | exact superpose eq12663 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12677 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq582 x y
       have i₂ := eq12663
       grind)
    | exact superpose eq12663 eq582
    | (have j0 := eq582 x y
       grind)
    | exact resolve eq582 eq12663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12663
  have eq12683 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12677
  have eq12684 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12672
  have eq12689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12683
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12683
    | exact resolve eq12683 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12683
  have eq12694 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12684
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12684
    | exact resolve eq12684 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12684
  have eq12695 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12694
  have eq12708 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12689
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12689
    | exact resolve eq12689 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12689
  have eq12716 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12708
    | exact resolve eq12708 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708
  have eq12717 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12716
  have eq12725 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12717
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12717
    | exact resolve eq12717 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12717
  have eq12733 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12725
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12725
    | exact resolve eq12725 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12864 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12695
       grind)
    | exact superpose eq12695 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12695
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12695
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12695
       grind)
    | exact resolve eq12 eq12695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12695
  have eq12892 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12864
  have eq12898 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12892
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12892
    | exact resolve eq12892 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12892
  have eq12899 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12898
  have eq12900 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12899
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12899
    | exact resolve eq12899 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12899
  have eq12991 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12733 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12733
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12733
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12733
       grind)
    | exact resolve eq12 eq12733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12733
  have eq13019 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12991
  have eq13025 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13019
    | exact resolve eq13019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13019
  have eq13026 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13025
  have eq13027 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13026
    | exact resolve eq13026 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq13381 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52
       have i₂ := eq12900
       grind)
    | exact superpose eq12900 eq52
    | exact resolve eq52 eq12900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12900
  have eq13411 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13381
    | exact resolve eq13381 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13381
  have eq14123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13411 eq13027
    | exact resolve eq13027 eq13411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13027 eq13411
  have eq14133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14123
  have eq14135 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14133
       have r₂ := eq27
       grind)
    | exact resolve eq14133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14133
  have eq14258 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14135 eq63
    | (have r₁ := eq63
       have r₂ := eq14135
       grind)
    | exact resolve eq63 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq14135
  have eq14274 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14258
  have eq14340 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14274 eq61
    | exact resolve eq61 eq14274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq14274
  have eq14370 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14340
    | exact resolve eq14340 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14340
  have eq14374 : y = (k x y) := by
    first
    | (have r₁ := eq14370
       have r₂ := eq62
       grind)
    | exact resolve eq14370 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq14370
  have eq14377 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq52
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq52
    | exact resolve eq52 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14385 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14390 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq582 y x
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq582
    | (have j0 := eq582 y x
       grind)
    | exact resolve eq582 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq14396 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14390
  have eq14397 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq14385
  have eq14402 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14396
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14396
    | exact resolve eq14396 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14396
  have eq14407 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14397
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14397
    | exact resolve eq14397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14397
  have eq14414 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq14377
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14377
    | exact resolve eq14377 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377
  have eq14419 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14402
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14402
    | exact resolve eq14402 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14402
  have eq14427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14419
    | exact resolve eq14419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14419
  have eq14435 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14427
    | exact resolve eq14427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14427
  have eq14443 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14435
    | exact resolve eq14435 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14435
  have eq14524 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq461 x
       have i₂ := eq14407
       grind)
    | exact superpose eq14407 eq461
    | exact resolve eq461 eq14407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq14526 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq221 y
       have i₂ := eq14407
       grind)
    | exact superpose eq14407 eq221
    | exact resolve eq221 eq14407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq14527 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14407
       grind)
    | exact superpose eq14407 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14407
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14407
       grind)
    | exact resolve eq12 eq14407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14407
  have eq14555 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq14527
  have eq14561 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14555
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14555
    | exact resolve eq14555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14555
  have eq14562 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq14561
  have eq14563 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14562
       have i₂ := eq14374
       grind)
    | exact superpose eq14374 eq14562
    | exact resolve eq14562 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14374 eq14562
  have eq14564 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14563
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14563
    | exact resolve eq14563 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14563
  have eq14635 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq14911 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14564 eq14524
    | exact resolve eq14524 eq14564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14524
  have eq14935 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14911
       have r₂ := eq14635
       grind)
    | exact resolve eq14911 eq14635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911
  have eq14936 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14564 eq14526
    | exact resolve eq14526 eq14564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14526 eq14564
  have eq14980 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14936
       have r₂ := eq14635
       grind)
    | exact resolve eq14936 eq14635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14936
  have eq16109 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14935
       have i₂ := eq14980
       grind)
    | exact superpose eq14980 eq14935
    | exact resolve eq14935 eq14980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14935 eq14980
  have eq16138 : x = y ∨ x = (M.op x y) := by grind
  clear eq16109
  have eq16140 : x = (M.op x y) := by
    first
    | (have r₁ := eq16138
       have r₂ := eq14635
       grind)
    | exact resolve eq16138 eq14635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14635 eq16138
  have eq16143 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16140 eq20
    | exact resolve eq20 eq16140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16161 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16140 eq125
    | exact resolve eq125 eq16140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq16140
  have eq16256 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq16161
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16161
    | exact resolve eq16161 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq16161
  have eq16268 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16143
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16143
    | exact resolve eq16143 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16143
  have eq16276 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14414 eq16256
    | exact resolve eq16256 eq14414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14414 eq16256
  have eq16285 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16268 eq26
    | exact resolve eq26 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq16353 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16268 eq14443
    | exact resolve eq14443 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14443
  have eq16356 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq16353
       have r₂ := eq27
       grind)
    | exact resolve eq16353 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq16476 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq16356 eq629
    | exact resolve eq629 eq16356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16477 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16356 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq16356
       grind)
    | exact resolve eq12 eq16356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16505 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq16477
  have eq16507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16285 eq16505
    | exact resolve eq16505 eq16285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16505
  have eq16508 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq16268 eq16476
    | exact resolve eq16476 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16509 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq16507
       have r₂ := eq27
       grind)
    | exact resolve eq16507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16507
  have eq16510 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16285 eq16509
    | exact resolve eq16509 eq16285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16285 eq16509
  have eq16511 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16276 eq16510
    | exact resolve eq16510 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16276 eq16510
  have eq16513 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq16511 eq27
    | exact resolve eq27 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq16606 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16511 eq16508
    | exact resolve eq16508 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16508
  have eq16743 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16606 eq629
    | exact resolve eq629 eq16606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq16606
  have eq16769 : (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq16511 eq16743
    | exact resolve eq16743 eq16511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16511 eq16743
  have eq16771 : (σ x) = (σ y) := by
    first
    | exact superpose eq16356 eq16769
    | exact resolve eq16769 eq16356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16356 eq16769
  have eq16772 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16268 eq16771
    | exact resolve eq16771 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16268 eq16771
  have eq16773 : False := by grind
  exact eq16773

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,X) = X then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyy_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq130 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq59
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq59
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq136 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq134
    | exact resolve eq134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq388 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59 eq388
    | exact resolve eq388 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq388
  have eq747 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have j0 := eq99 (M.op x y) y
       grind)
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq748 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have j0 := eq99 x (M.op x y)
       grind)
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq754 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq748
  have eq755 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq747
  have eq839 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq755 eq121
    | (have j0 := eq121 y (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq121 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq754 eq121
    | (have j0 := eq121 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq121 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq10
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq10 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq896 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | (have j0 := eq873 X0 X1
       grind)
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq911 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq840
    | exact resolve eq840 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq912 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq839
    | exact resolve eq839 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq929 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq911
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq911
    | exact resolve eq911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq930 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq912
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq912
    | exact resolve eq912 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq937 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq929
    | exact resolve eq929 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq938 : (σ y) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq930
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq930
    | exact resolve eq930 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq941 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq937
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq937
    | exact resolve eq937 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq942 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq938
       have i₂ := eq140 sF0
       grind)
    | exact superpose eq140 eq938
    | exact resolve eq938 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq944 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq941
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq941
    | exact resolve eq941 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq945 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq942
    | exact resolve eq942 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq947 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq944
    | exact resolve eq944 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq948 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq945
       have i₂ := eq140 sF0
       grind)
    | exact superpose eq140 eq945
    | exact resolve eq945 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq951 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq947
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq947
    | exact resolve eq947 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq952 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq948
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq948
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq948
    | exact resolve eq948 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq954 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq951
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq951
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq951
    | exact resolve eq951 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq955 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq952
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq952
    | exact resolve eq952 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq957 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq954
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq954
    | exact resolve eq954 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq958 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq955
    | exact resolve eq955 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1793 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1804 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq754 eq1793
    | exact resolve eq1793 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1819 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1804
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1804
    | exact resolve eq1804 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq2516 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2525 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq755 eq2516
    | exact resolve eq2516 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2540 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq2525
    | exact resolve eq2525 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525
  have eq36149 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq754
       have i₂ := eq896 sF0 (M.op x x)
       grind)
    | exact superpose eq896 eq754
    | (have j1 := eq896 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq754 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq896
  have eq36598 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36149
    | exact resolve eq36149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36149
  have eq36885 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36598
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq36598
    | exact resolve eq36598 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36598
  have eq37049 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36885
    | exact resolve eq36885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36885
  have eq37156 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq37049
    | exact resolve eq37049 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37049
  have eq37216 : (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37156
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq37156
    | exact resolve eq37156 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37156
  have eq37271 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37216
       have i₂ := eq53 (σ x) (σ x) (σ x)
       grind)
    | (have i₁ := eq37216
       have i₂ := eq53 x (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) x
       grind)
    | exact superpose eq53 eq37216
    | exact resolve eq37216 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37216
  have eq37316 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37271
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37271
    | exact resolve eq37271 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37271
  have eq74111 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq957 eq53
    | exact resolve eq53 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75994 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37316 eq53
    | exact resolve eq53 eq37316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37316
  have eq76190 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq958 eq54
    | exact resolve eq54 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq76193 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq958 eq53
    | exact resolve eq53 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq80674 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76193 eq78
    | exact resolve eq78 eq76193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq76193
  have eq80719 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq80674 eq53
    | exact resolve eq53 eq80674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80674
  have eq80736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80719 eq74111
    | exact resolve eq74111 eq80719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74111 eq80719
  have eq80769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq80736
    | exact resolve eq80736 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80736
  have eq80773 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq80769
       have r₂ := eq27
       grind)
    | exact resolve eq80769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80769
  have eq80786 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80773 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq80773
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq80773
       grind)
    | exact resolve eq13 eq80773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80773
  have eq80799 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80786
  have eq80811 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80799
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq80799
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq80799
    | exact resolve eq80799 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80799
  have eq80812 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80811
  have eq80821 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1819 eq80812
    | exact resolve eq80812 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80812
  have eq80822 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80821
  have eq80833 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq80822 eq82
    | exact resolve eq82 eq80822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq80822
  have eq81046 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76190 eq80833
    | exact resolve eq80833 eq76190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76190
  have eq81079 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq81046
  have eq94470 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq81079 eq80833
    | exact resolve eq80833 eq81079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80833 eq81079
  have eq94488 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq94470
  have eq98988 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq94488 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq94488
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq94488
       grind)
    | exact resolve eq13 eq94488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94488
  have eq99001 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq98988
  have eq99021 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq99001
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq99001
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq99001
    | exact resolve eq99001 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99001
  have eq99022 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq99021
  have eq99031 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2540 eq99022
    | exact resolve eq99022 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99022
  have eq99032 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq99031
  have eq99047 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq99032 eq53
    | exact resolve eq53 eq99032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99032
  have eq99083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq957 eq99047
    | exact resolve eq99047 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq99047
  have eq99132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by grind
  clear eq99083
  have eq99142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq99132
    | exact resolve eq99132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99132
  have eq99147 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq99142
       have r₂ := eq27
       grind)
    | exact resolve eq99142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99142
  have eq99252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq99147 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq99147
       grind)
    | exact resolve eq13 eq99147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99147
  have eq99265 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq99252
  have eq99280 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq99265
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq99265
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq99265
    | exact resolve eq99265 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99265
  have eq99281 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq99280
  have eq99290 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1819 eq99281
    | exact resolve eq99281 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99281
  have eq99291 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq99290
  have eq99299 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq99291 eq39
    | exact resolve eq39 eq99291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq99291
  have eq99367 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq99299
    | exact resolve eq99299 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99299
  have eq99375 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99367 eq38
    | exact resolve eq38 eq99367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99367
  have eq99447 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq99375
    | exact resolve eq99375 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99375
  have eq99451 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99447 eq20
    | exact resolve eq20 eq99447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99452 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq99447 eq77
    | exact resolve eq77 eq99447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq99542 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq99556 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99451
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99451
    | exact resolve eq99451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99451
  have eq100310 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99452 (M.op y x)
       have i₂ := eq99452 x
       grind)
    | exact superpose eq99452 eq99452
    | exact resolve eq99452 eq99452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99452
  have eq100341 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq100310
  have eq100403 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq100341
       grind)
    | exact superpose eq100341 eq140
    | exact resolve eq140 eq100341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100341
  have eq100448 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100403
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100403
    | exact resolve eq100403 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100403
  have eq100463 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99556 eq100448
    | exact resolve eq100448 eq99556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99556 eq100448
  have eq100535 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq100463
  have eq100846 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100535 eq2540
    | exact resolve eq2540 eq100535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq100535
  have eq100925 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq100846
    | exact resolve eq100846 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq100846
  have eq101143 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq99447 eq100925
    | exact resolve eq100925 eq99447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99447 eq100925
  have eq101250 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq101143
       have r₂ := eq99542
       grind)
    | exact resolve eq101143 eq99542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99542 eq101143
  have eq101255 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101250
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq101250
    | exact resolve eq101250 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq101250
  have eq101258 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101255
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq101255
    | exact resolve eq101255 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101255
  have eq101260 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101258
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq101258
    | exact resolve eq101258 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq101258
  have eq101331 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq101260 eq53
    | exact resolve eq53 eq101260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101260
  have eq104567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101331 eq75994
    | exact resolve eq75994 eq101331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75994 eq101331
  have eq104593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq104567
  have eq104610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq104593
    | exact resolve eq104593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104593
  have eq104616 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq104610
       have r₂ := eq27
       grind)
    | exact resolve eq104610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104610
  have eq105592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104616 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (M.op (σ x) (σ x))
       have r₂ := eq104616
       grind)
    | exact resolve eq13 eq104616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104616
  have eq105605 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq105592
  have eq105620 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105605
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq105605
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq105605
    | exact resolve eq105605 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq105605
  have eq105629 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1819 eq105620
    | exact resolve eq105620 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819 eq105620
  have eq105630 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq105629
  have eq105641 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105630 eq38
    | exact resolve eq38 eq105630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq105630
  have eq105729 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq105641
    | exact resolve eq105641 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq105641
  have eq105730 : x = (M.op x y) := by grind
  clear eq105729
  have eq105735 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq105730 eq20
    | exact resolve eq20 eq105730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq105744 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq105730 eq80
    | exact resolve eq80 eq105730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq105806 : x = (k y (M.op x x)) := by
    first
    | exact superpose eq105730 eq755
    | exact resolve eq755 eq105730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq105730
  have eq119765 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq105735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105735
    | exact resolve eq105735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105735
  have eq120178 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq119765 eq22
    | exact resolve eq22 eq119765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq120179 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq119765 eq26
    | exact resolve eq26 eq119765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq120191 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119765 eq136
    | exact resolve eq136 eq119765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq120199 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq119765 eq391
    | exact resolve eq391 eq119765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq119765
  have eq125446 : x = (M.op x x) := by
    first
    | (have i₁ := eq105744 (M.op x x)
       have i₂ := eq105744 x
       grind)
    | exact superpose eq105744 eq105744
    | exact resolve eq105744 eq105744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105744
  have eq125570 : x = (k y x) := by
    first
    | (have i₁ := eq105806
       have i₂ := eq125446
       grind)
    | exact superpose eq125446 eq105806
    | exact resolve eq105806 eq125446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105806
  have eq125754 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120191
       have i₂ := eq125570
       grind)
    | exact superpose eq125570 eq120191
    | exact resolve eq120191 eq125570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120191
  have eq125755 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120199
       have i₂ := eq125570
       grind)
    | exact superpose eq125570 eq120199
    | exact resolve eq120199 eq125570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120199 eq125570
  have eq125819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq125755
       have i₂ := eq120178
       grind)
    | exact superpose eq120178 eq125755
    | exact resolve eq125755 eq120178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125755
  have eq125820 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq125754
       have i₂ := eq120178
       grind)
    | exact superpose eq120178 eq125754
    | exact resolve eq125754 eq120178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125754
  have eq125843 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq125819
       have r₂ := eq27
       grind)
    | exact resolve eq125819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125819
  have eq125886 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq125446
       grind)
    | exact superpose eq125446 eq140
    | exact resolve eq140 eq125446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq125446
  have eq125994 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq125886
       have i₂ := eq120178
       grind)
    | exact superpose eq120178 eq125886
    | exact resolve eq125886 eq120178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120178 eq125886
  have eq126267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125994 eq125820
    | exact resolve eq125820 eq125994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125820
  have eq126275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125994 eq125843
    | exact resolve eq125843 eq125994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125843
  have eq126294 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq126275
       have r₂ := eq27
       grind)
    | exact resolve eq126275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126275
  have eq126299 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq126267
       have r₂ := eq27
       grind)
    | exact resolve eq126267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126267
  have eq133104 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq126299
       have r₂ := eq126294
       grind)
    | exact resolve eq126299 eq126294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126294 eq126299
  have eq133787 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq133104 eq120179
    | exact resolve eq120179 eq133104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120179 eq133104
  have eq136082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125994 eq133787
    | exact resolve eq133787 eq125994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125994 eq133787
  have eq136528 : False := by grind
  exact eq136528
