import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq580 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq634 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq611
    | (have j0 := eq611 X0 X1
       grind)
    | exact resolve eq611 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq651 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq634 x y
       grind)
    | exact superpose eq634 eq16
    | (have j1 := eq634 x y
       grind)
    | exact resolve eq16 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq3931 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq608 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq608
    | exact resolve eq608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq3995 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3931 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3931
    | (have j0 := eq3931 X0 X1
       grind)
    | exact resolve eq3931 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931
  have eq6162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq651
       have i₂ := eq3995 y x
       grind)
    | exact superpose eq3995 eq651
    | (have j1 := eq3995 y x
       grind)
    | (have r₁ := eq651
       have r₂ := eq3995 y x
       grind)
    | (have r₁ := eq651
       have r₂ := eq3995 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq651
       have r₂ := eq3995 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq651 eq3995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq3995
  have eq6163 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6162
  have eq7907 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq656 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq656
    | (have j0 := eq656 (τ X0) (τ X1)
       grind)
    | exact resolve eq656 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7974 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7907 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7907
    | (have j0 := eq7907 X0 X1
       grind)
    | exact resolve eq7907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907
  have eq8009 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7974 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7974
    | (have j0 := eq7974 X0 X1
       grind)
    | exact resolve eq7974 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7974
  have eq8041 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8009 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8009
    | (have j0 := eq8009 X0 X1
       grind)
    | exact resolve eq8009 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq8067 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8041 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8041
    | (have j0 := eq8041 X0 X1
       grind)
    | exact resolve eq8041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8041
  have eq8086 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8067 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq8067
    | (have j0 := eq8067 X0 X1
       grind)
    | exact resolve eq8067 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8067
  have eq8103 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8086 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8086
    | (have j0 := eq8086 X0 X1
       grind)
    | exact resolve eq8086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086
  have eq8116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8103 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8103
    | (have j0 := eq8103 X0 X1
       grind)
    | exact resolve eq8103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8103
  have eq29375 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6163
       grind)
    | exact superpose eq6163 eq16
    | exact resolve eq16 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq29376 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq29375
       have r₂ := eq22 x
       grind)
    | exact resolve eq29375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29375
  have eq29377 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq29376
       grind)
    | exact superpose eq29376 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq29376
       grind)
    | exact resolve eq13 eq29376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29376
  have eq29411 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq29377
  have eq33197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29411
       grind)
    | exact superpose eq29411 eq16
    | exact resolve eq16 eq29411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29411
  have eq33198 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq33197
       have r₂ := eq22 x
       grind)
    | exact resolve eq33197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33197
  have eq33202 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq656 x y
       have i₂ := eq33198
       grind)
    | exact superpose eq33198 eq656
    | (have j0 := eq656 x y
       grind)
    | exact resolve eq656 eq33198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq33198
  have eq33231 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq33202
  have eq33232 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq33231
  have eq33237 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33232
       grind)
    | exact superpose eq33232 eq16
    | exact resolve eq16 eq33232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33238 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq580 x (σ y)
       have i₂ := eq33232
       grind)
    | exact superpose eq33232 eq580
    | (have j0 := eq580 x (σ y)
       grind)
    | (have r₁ := eq580 x (σ y)
       have r₂ := eq33232
       grind)
    | exact resolve eq580 eq33232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq33232
  have eq33293 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq33238
  have eq33294 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq33293
  have eq33300 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33294
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq33294
    | exact resolve eq33294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33294
  have eq33585 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq33300
       grind)
    | exact superpose eq33300 eq10
    | exact resolve eq10 eq33300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33300
  have eq33777 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33585
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33585
    | exact resolve eq33585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33585
  have eq33779 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33777
       grind)
    | exact superpose eq33777 eq16
    | exact resolve eq16 eq33777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33777
  have eq33780 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq33779
       have r₂ := eq22 x
       grind)
    | exact resolve eq33779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33779
  have eq33794 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq33780
       grind)
    | exact superpose eq33780 eq10
    | exact resolve eq10 eq33780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33780
  have eq33987 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq33794
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq33794
    | exact resolve eq33794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33794
  have eq34017 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq8116 x y
       have i₂ := eq33987
       grind)
    | exact superpose eq33987 eq8116
    | (have j0 := eq8116 x y
       grind)
    | (have r₁ := eq8116 x y
       have r₂ := eq33987
       grind)
    | exact resolve eq8116 eq33987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8116 eq33987
  have eq34021 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq34017
  have eq34025 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34021
       grind)
    | exact superpose eq34021 eq16
    | exact resolve eq16 eq34021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34021
  have eq34028 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq34025
       have r₂ := eq22 x
       grind)
    | exact resolve eq34025 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34025
  have eq34029 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33237
       have i₂ := eq34028
       grind)
    | exact superpose eq34028 eq33237
    | exact resolve eq33237 eq34028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33237
  have eq34067 : (σ x) = (σ y) := by grind
  clear eq34029
  have eq34068 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34067
       grind)
    | exact superpose eq34067 eq16
    | exact resolve eq16 eq34067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34067
  have eq34262 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34068
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq34068
    | exact resolve eq34068 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq34068
  have eq34263 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34262
       have i₂ := eq34028
       grind)
    | exact superpose eq34028 eq34262
    | exact resolve eq34262 eq34028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34028 eq34262
  have eq34264 : False := by grind
  exact eq34264

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq530
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq530
    | exact resolve eq530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1178 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1178
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1178
    | exact resolve eq1178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1199 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1189
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1189
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1189
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1189
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1189
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1189 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1189
  have eq1201 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1199
  have eq1273 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq9
    | exact resolve eq9 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1274 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1273
  have eq1275 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1274
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1274
    | exact resolve eq1274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1276 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1275
  have eq1277 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1276
  have eq1355 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq10
    | exact resolve eq10 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1358 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1355
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1355
    | exact resolve eq1355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1359 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1358
  have eq1362 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1359
       grind)
    | exact superpose eq1359 eq22
    | exact resolve eq22 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1408 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1362
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1362
    | exact resolve eq1362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1362
  have eq1429 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq538
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq538
    | (have r₁ := eq538
       have r₂ := eq1408
       grind)
    | exact resolve eq538 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq1408
  have eq1433 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1429
  have eq1453 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1433
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1433
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1433
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1433
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1433
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1433 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1433
  have eq1454 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1453
  have eq1455 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1454
  have eq1457 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1455
       have r₂ := eq1359
       grind)
    | exact resolve eq1455 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq1455
  have eq1458 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1457
       grind)
    | exact superpose eq1457 eq9
    | exact resolve eq9 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1459 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1458
  have eq1460 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1459
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1459
    | exact resolve eq1459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1461 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1460
  have eq1462 : (σ x) = (σ y) := by grind
  clear eq1461
  have eq1464 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1462
       grind)
    | exact superpose eq1462 eq15
    | exact resolve eq15 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1509 : x = y := by
    first
    | (have i₁ := eq1464
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1464
    | exact resolve eq1464 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1512 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1509
       grind)
    | exact superpose eq1509 eq9
    | exact resolve eq9 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1513 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1512
  have eq1514 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1513
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1513
    | exact resolve eq1513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq1515 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1514
  have eq1516 : False := by grind
  exact eq1516

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq732 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq774 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq773 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq774 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq1038 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1032 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1032 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1032 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq1032 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq1032 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1093 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1038 X0 (τ X1)
       grind)
    | exact superpose eq1038 eq19
    | (have j1 := eq1038 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1038 (σ X0) (σ X1)
       grind)
    | exact superpose eq1038 eq15
    | (have j1 := eq1038 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1203 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1093
    | exact resolve eq1093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1251 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1203
    | (have j0 := eq1203 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1450 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1101 x y
       grind)
    | exact superpose eq1101 eq16
    | (have j1 := eq1101 x y
       grind)
    | exact resolve eq16 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1450
       have i₂ := eq1251 y x
       grind)
    | exact superpose eq1251 eq1450
    | (have j1 := eq1251 (σ x) (σ y)
       grind)
    | (have r₁ := eq1450
       have r₂ := eq1251 y x
       grind)
    | (have r₁ := eq1450
       have r₂ := eq1251 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1450
       have r₂ := eq1251 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1450 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1450
  have eq1481 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1480
  have eq1485 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq10
    | exact resolve eq10 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1528 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1485
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1485
    | exact resolve eq1485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485
  have eq1529 : x = y := by grind
  clear eq1528
  have eq1531 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq16
    | exact resolve eq16 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1532 : False := by grind
  exact eq1532

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation446 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq196 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq213 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq109 X1 X0 X3
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq713 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1817 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1879 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1817 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1817
    | (have j0 := eq1817 X0 X1
       grind)
    | exact resolve eq1817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq713
       have i₂ := eq1879 x y
       grind)
    | exact superpose eq1879 eq713
    | (have j1 := eq1879 x y
       grind)
    | (have r₁ := eq713
       have r₂ := eq1879 x y
       grind)
    | (have r₁ := eq713
       have r₂ := eq1879 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq713
       have r₂ := eq1879 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq713 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1879
  have eq2265 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2264
  have eq7354 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq213 x X2 X0 X1
       grind)
    | exact superpose eq213 eq9
    | exact resolve eq9 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq7429 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq7354 x X1 X0
       grind)
    | exact superpose eq7354 eq9
    | exact resolve eq9 eq7354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354
  have eq9430 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2265
       grind)
    | exact superpose eq2265 eq16
    | exact resolve eq16 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265
  have eq9431 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq9430
       have r₂ := eq23 x
       grind)
    | exact resolve eq9430 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9430
  have eq9433 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9431
       grind)
    | exact superpose eq9431 eq10
    | exact resolve eq10 eq9431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9431
  have eq9487 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9433
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9433
    | exact resolve eq9433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433
  have eq9489 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9487
       grind)
    | exact superpose eq9487 eq16
    | exact resolve eq16 eq9487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9487
  have eq9490 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9489
       have r₂ := eq23 x
       grind)
    | exact resolve eq9489 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq9489
  have eq9506 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq9490
       grind)
    | exact superpose eq9490 eq10
    | exact resolve eq10 eq9490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9490
  have eq9560 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9506
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9506
    | exact resolve eq9506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9506
  have eq9561 : x = (M.op y y) := by grind
  clear eq9560
  have eq9571 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq9561
       grind)
    | exact superpose eq9561 eq111
    | exact resolve eq111 eq9561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq9622 : x = (M.op x y) := by
    first
    | (have i₁ := eq7429 y y
       have i₂ := eq9561
       grind)
    | exact superpose eq9561 eq7429
    | exact resolve eq7429 eq9561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7429 eq9561
  have eq9676 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9571
       grind)
    | exact superpose eq9571 eq16
    | exact resolve eq16 eq9571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9571
  have eq9708 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9676
       have i₂ := eq9622
       grind)
    | exact superpose eq9622 eq9676
    | exact resolve eq9676 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622 eq9676
  have eq9709 : False := by grind
  exact eq9709

/-- `Equation4466`: `x ◇ (y ◇ x) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4466 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4466 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4466.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq180 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq177
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq177
    | exact resolve eq177 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq207
  have eq225 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq125 (M.op sF1 sF1)
       have i₂ := eq175 sF1
       grind)
    | exact superpose eq175 eq125
    | exact resolve eq125 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq175
  have eq236 : (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq29 eq225
    | exact resolve eq225 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq691 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op x X4)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op X4 X5) X4
       have i₂ := eq16 X0 X1 X4 X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X4 X5)) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq692 x x X2 X3 X4 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq697 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X1) X0) X4) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq691 X0 X1 x x X4
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq691
    | exact resolve eq691 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq699 : ∀ X4 X5 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X4 X5)) := by
    intro X4 X5
    first
    | (have i₁ := eq696 x x X4 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq696
    | exact resolve eq696 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X1) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 (M.op X0 X1) X1
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op x y) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq693 X2 (M.op X2 x)
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq693
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : (M.op (M.op x y) x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq693 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq693
    | (have j0 := eq693 y x
       grind)
    | exact resolve eq693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : (M.op (M.op x y) x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 (σ y) (σ x)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op x y) x) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op x X2)
       have i₂ := eq693 X2 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X1) (M.op (M.op x y) x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X2
    first
    | (have i₁ := eq707 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq707
    | exact resolve eq707 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq710 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op X2 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X2
    first
    | (have i₁ := eq702 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq702
    | exact resolve eq702 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq728 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op X0 x)
       have i₂ := eq706 X0 x
       grind)
    | (have i₁ := eq693 x (M.op x y)
       have i₂ := eq706 x x
       grind)
    | exact superpose eq706 eq693
    | exact resolve eq693 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq709 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | exact resolve eq28 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) ≠ X0 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq709 eq13
    | (have j0 := eq13 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) x) (M.op (M.op (σ x) (σ y)) (σ x))
       have r₂ := eq709 (M.op (M.op x y) x)
       grind)
    | exact resolve eq13 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq792 : ∀ X0 : G, (M.op (M.op x y) x) ≠ X0 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq728 eq781
    | (have j0 := eq781 X0
       grind)
    | (have r₁ := eq781 (M.op (M.op x y) x)
       have r₂ := eq728
       grind)
    | exact resolve eq781 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq793 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq780 X0
       grind)
    | (have r₁ := eq780 X0
       have r₂ := eq728
       grind)
    | exact resolve eq780 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq808 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq706
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq848 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq808 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq865 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq848 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq848 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq848 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq878 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq837 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq837
    | (have j0 := eq837 (σ X0)
       grind)
    | exact resolve eq837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq793 eq35
    | exact resolve eq35 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq897 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq883 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq883
    | exact resolve eq883 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq944 : (σ (M.op (M.op x y) x)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq897 eq837
    | (have j0 := eq837 (σ (M.op (M.op x y) x))
       grind)
    | (have r₁ := eq837 (σ (M.op (M.op x y) x))
       have r₂ := eq897 (σ (M.op (M.op x y) x))
       grind)
    | exact resolve eq837 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq944
  have eq1011 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op (σ x) (σ y)) (σ x)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq710 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1020 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq728 eq1011
    | (have j0 := eq1011 X0
       grind)
    | exact resolve eq1011 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1025 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq1020 X0
       have j1 := eq28 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq1020 x
       have r₂ := eq28 X0 x
       grind)
    | (have r₁ := eq1020 (M.op (M.op (σ x) (σ y)) (σ x))
       have r₂ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ x))
       grind)
    | (have r₁ := eq1020 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))))
       have r₂ := eq28 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x)))
       grind)
    | exact resolve eq1020 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1028 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = X0 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq699 eq1025
    | (have j0 := eq1025 X0
       grind)
    | exact resolve eq1025 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1025
  have eq1030 : ∀ X0 : G, (M.op (M.op x y) x) = X0 ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq728 eq1028
    | (have j0 := eq1028 X0
       grind)
    | exact resolve eq1028 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1032 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq1030 (k (M.op (M.op x y) x) X0)
       have j1 := eq792 X0
       grind)
    | (have r₁ := eq1030 X0
       have r₂ := eq792 X0
       grind)
    | (have r₁ := eq1030 (M.op (M.op x y) x)
       have r₂ := eq792 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq1030 X0
       have r₂ := eq792 (k (M.op (M.op x y) x) X0)
       grind)
    | exact resolve eq1030 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq1030
  have eq2808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq40
    | exact resolve eq40 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2809 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2808
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2808
    | exact resolve eq2808 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq2811 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2809
    | exact resolve eq2809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809
  have eq19803 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    intro X0 X1
    first
    | exact superpose eq957 eq708
    | exact resolve eq708 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19808 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) x)) = (σ (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq957 eq19803
    | exact resolve eq19803 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19803
  have eq19823 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq700 eq19808
    | exact resolve eq19808 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq19808
  have eq19878 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq19823 eq15
    | exact resolve eq15 eq19823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2811 eq830
    | exact resolve eq830 eq2811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23352 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23345
       have r₂ := eq27
       grind)
    | exact resolve eq23345 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23345
  have eq23359 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23352 eq218
    | exact resolve eq218 eq23352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23352
  have eq23395 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq23359
    | exact resolve eq23359 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23359
  have eq23407 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq23395
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq23395
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq23395
       have r₂ := eq13 y x
       grind)
    | exact resolve eq23395 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23395
  have eq23411 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq23407
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq23407
       have r₂ := eq28 x x
       grind)
    | exact resolve eq23407 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23407
  have eq23413 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq23411 eq200
    | exact resolve eq200 eq23411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23411
  have eq23448 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq23413
    | exact resolve eq23413 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23413
  have eq23460 : y = (k y x) := by
    first
    | (have j1 := eq865 x y
       grind)
    | (have r₁ := eq23448
       have r₂ := eq865 x x
       grind)
    | exact resolve eq23448 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23448
  have eq23469 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq823
       have i₂ := eq23460
       grind)
    | exact superpose eq23460 eq823
    | exact resolve eq823 eq23460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq23471 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq23460
       grind)
    | exact superpose eq23460 eq40
    | exact resolve eq40 eq23460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq23460
  have eq23472 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq23471
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23471
    | exact resolve eq23471 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23471
  have eq23479 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23472 eq2811
    | exact resolve eq2811 eq23472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2811
  have eq23482 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23472 eq830
    | exact resolve eq830 eq23472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq23472
  have eq23604 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23469
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq23469
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq23469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23609 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq23469
       grind)
    | exact superpose eq23469 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq23469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23623 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23469
       grind)
    | exact superpose eq23469 eq706
    | exact resolve eq706 eq23469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23469
  have eq23625 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq23609
  have eq23626 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq23604
  have eq23627 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23623
    | exact resolve eq23623 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623
  have eq23640 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23625 eq23626
    | exact resolve eq23626 eq23625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23625 eq23626
  have eq23641 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq23640
  have eq23672 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23479
       grind)
    | exact superpose eq23479 eq706
    | exact resolve eq706 eq23479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23479
  have eq23676 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23672
    | exact resolve eq23672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23672
  have eq23703 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23482
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq23482
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq23482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23708 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23482 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq23482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23722 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23482 eq706
    | exact resolve eq706 eq23482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23482
  have eq23724 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23708
  have eq23725 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq23703
  have eq23727 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23722
    | exact resolve eq23722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23722
  have eq23740 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23724 eq23725
    | exact resolve eq23725 eq23724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23724 eq23725
  have eq23741 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23740
  have eq23765 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23627 eq793
    | exact resolve eq793 eq23627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23836 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23627 eq19823
    | exact resolve eq19823 eq23627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23837 : x = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23627 eq19878
    | exact resolve eq19878 eq23627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23627
  have eq23869 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq23836
    | exact resolve eq23836 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23836
  have eq24208 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq697 x x X0
       have i₂ := eq23869
       grind)
    | exact superpose eq23869 eq697
    | exact resolve eq697 eq23869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24212 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq23869
       grind)
    | exact superpose eq23869 eq706
    | exact resolve eq706 eq23869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24216 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23869 eq24212
    | exact resolve eq24212 eq23869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24212
  have eq24219 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq728 eq24208
    | exact resolve eq24208 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24208
  have eq24232 : ∀ X0 : G, x = (M.op (M.op x x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24216 eq24219
    | exact resolve eq24219 eq24216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24219
  have eq24240 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23869 eq24232
    | exact resolve eq24232 eq23869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23869 eq24232
  have eq24807 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24216 eq19823
    | exact resolve eq19823 eq24216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24216
  have eq24845 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24807
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24807
    | exact resolve eq24807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24807
  have eq24964 : (M.op x y) = (τ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24845 eq29
    | exact resolve eq29 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25302 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24240 y
       grind)
    | exact superpose eq24240 eq18
    | (have j1 := eq24240 y
       grind)
    | exact resolve eq18 eq24240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24240
  have eq25382 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25302 eq29
    | exact resolve eq29 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302
  have eq26761 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq23837
       grind)
    | exact superpose eq23837 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq23837
       grind)
    | exact resolve eq28 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26763 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq23837
       grind)
    | exact superpose eq23837 eq16
    | exact resolve eq16 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26779 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26761
  have eq26791 : (M.op x x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26763 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq26763
    | exact resolve eq26763 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26763
  have eq26793 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25382 eq26779
    | exact resolve eq26779 eq25382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25382 eq26779
  have eq26801 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq728 eq26791
    | exact resolve eq26791 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26791
  have eq26804 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23837 eq26801
    | exact resolve eq26801 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837 eq26801
  have eq26805 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24964 eq26804
    | exact resolve eq26804 eq24964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26804
  have eq26874 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26793 eq837
    | (have j0 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq26793 (M.op x y)
       grind)
    | exact resolve eq837 eq26793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26793
  have eq26931 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq26874
  have eq28129 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26931 eq706
    | exact resolve eq706 eq26931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28135 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24964 eq28129
    | exact resolve eq28129 eq24964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24964 eq28129
  have eq28150 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26805 eq28135
    | exact resolve eq28135 eq26805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26805 eq28135
  have eq28162 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26931 eq28150
    | exact resolve eq28150 eq26931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26931 eq28150
  have eq28192 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28162 eq14
    | exact resolve eq14 eq28162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28162
  have eq28241 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq28192
    | exact resolve eq28192 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28192
  have eq28247 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28241 eq30
    | exact resolve eq30 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28409 : (σ x) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24845 eq28247
    | exact resolve eq28247 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845 eq28247
  have eq28460 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28241 eq28409
    | exact resolve eq28409 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28241 eq28409
  have eq28565 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28460 eq14
    | exact resolve eq14 eq28460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28460
  have eq28641 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq28565
    | exact resolve eq28565 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28565
  have eq28642 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq28641
  have eq28679 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28642 eq29
    | exact resolve eq29 eq28642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq28714 : (M.op x y) = (k (M.op x y) (τ (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28642 eq236
    | exact resolve eq236 eq28642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq31316 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq23641
       grind)
    | exact superpose eq23641 eq41
    | exact resolve eq41 eq23641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23641
  have eq31331 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31316
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31316
    | exact resolve eq31316 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31316
  have eq31338 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31331
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31331
    | exact resolve eq31331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31331
  have eq31893 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23676 eq19823
    | exact resolve eq19823 eq23676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23676
  have eq31932 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq31893
    | exact resolve eq31893 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31893
  have eq32327 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq31932
       grind)
    | exact superpose eq31932 eq706
    | exact resolve eq706 eq31932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32332 : x = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31932 eq32327
    | exact resolve eq32327 eq31932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31932 eq32327
  have eq32599 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32332 eq19823
    | exact resolve eq19823 eq32332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32332
  have eq32645 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq32599
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32599
    | exact resolve eq32599 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32599
  have eq32846 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq32645
  have eq39259 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23727 eq793
    | exact resolve eq793 eq23727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq39330 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23727 eq19823
    | exact resolve eq19823 eq23727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23727
  have eq39671 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39330 eq706
    | exact resolve eq706 eq39330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39677 : (σ x) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39330 eq39671
    | exact resolve eq39671 eq39330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39330 eq39671
  have eq40114 : (σ x) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39677 eq19878
    | exact resolve eq19878 eq39677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39677
  have eq40162 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq40114
    | exact resolve eq40114 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40114
  have eq44191 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23741 eq116
    | exact resolve eq116 eq23741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq23741
  have eq44209 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq44191
    | exact resolve eq44191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44191
  have eq44492 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq23765 X1
       grind)
    | exact superpose eq23765 eq28
    | (have j0 := eq28 X0 x
       have j1 := eq23765 X1
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq23765 X0
       grind)
    | exact resolve eq28 eq23765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44503 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq697 x x X0
       have i₂ := eq23765 X1
       grind)
    | exact superpose eq23765 eq697
    | (have j1 := eq23765 X1
       grind)
    | exact resolve eq697 eq23765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44507 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq23765 X0
       grind)
    | exact superpose eq23765 eq706
    | (have j1 := eq23765 X0
       grind)
    | exact resolve eq706 eq23765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44510 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq44492 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44492
  have eq44512 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23765 eq44507
    | (have j0 := eq44507 X0
       have j1 := eq23765 X0
       grind)
    | exact resolve eq44507 eq23765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44507
  have eq44515 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op x x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq728 eq44503
    | (have j0 := eq44503 X0 X1
       grind)
    | exact resolve eq44503 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44503
  have eq44528 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq23765 eq44515
    | (have j0 := eq44515 X0 X1
       have j1 := eq23765 X1
       grind)
    | exact resolve eq44515 eq23765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23765 eq44515
  have eq44536 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44512 eq44528
    | (have j0 := eq44528 X0 X1
       have j1 := eq44512 X1
       grind)
    | exact resolve eq44528 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44528
  have eq46343 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq39259 (M.op X1 X1)
       grind)
    | exact superpose eq39259 eq28
    | (have j0 := eq28 X0 (σ x)
       have j1 := eq39259 X1
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq39259 X0
       grind)
    | exact resolve eq28 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46354 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1 x
       have i₂ := eq39259 (M.op X0 X1)
       grind)
    | exact superpose eq39259 eq697
    | (have j1 := eq39259 X1
       grind)
    | exact resolve eq697 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46358 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq39259 (M.op x x)
       grind)
    | exact superpose eq39259 eq706
    | (have j1 := eq39259 X0
       grind)
    | exact resolve eq706 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46362 : ∀ X0 X1 : G, (k X1 (M.op (σ x) (σ y))) = X1 ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq46343 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46343
  have eq46366 : ∀ X0 : G, (σ x) = (M.op (M.op x y) x) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39259 eq46358
    | (have j0 := eq46358 X0
       have j1 := eq39259 X0
       grind)
    | exact resolve eq46358 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46358
  have eq46369 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq728 eq46354
    | (have j0 := eq46354 X0 X1
       grind)
    | exact resolve eq46354 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46354
  have eq46382 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq46366 eq46369
    | (have j0 := eq46369 X0 X1
       have j1 := eq46366 X1
       grind)
    | exact resolve eq46369 eq46366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46369
  have eq46391 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq39259 eq46382
    | (have j0 := eq46382 X0 X1
       have j1 := eq39259 X1
       grind)
    | exact resolve eq46382 eq39259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39259 eq46382
  have eq46589 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44209 eq706
    | exact resolve eq706 eq44209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46596 : (σ x) = (M.op (M.op x y) x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44209 eq46589
    | exact resolve eq46589 eq44209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44209 eq46589
  have eq46629 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq44510 (k X0 X0) x
       grind)
    | exact superpose eq44510 eq837
    | (have j0 := eq837 (M.op x y)
       have j1 := eq44510 X0 x
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq44510 X0 (M.op x y)
       grind)
    | (have r₁ := eq837 x
       have r₂ := eq44510 x x
       grind)
    | exact resolve eq837 eq44510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44510
  have eq46698 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq46629 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46629
  have eq46884 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq897 X0
       have i₂ := eq44512 (M.op sF0 x)
       grind)
    | exact superpose eq44512 eq897
    | (have j1 := eq44512 X1
       grind)
    | exact resolve eq897 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq46886 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq957
       have i₂ := eq44512 (M.op sF0 x)
       grind)
    | exact superpose eq44512 eq957
    | (have j1 := eq44512 X0
       grind)
    | exact resolve eq957 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq46948 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19823
       have i₂ := eq44512 (M.op sF0 x)
       grind)
    | exact superpose eq44512 eq19823
    | (have j1 := eq44512 X0
       grind)
    | exact resolve eq19823 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47002 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46948 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46948
    | (have j0 := eq46948 X0
       grind)
    | exact resolve eq46948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46948
  have eq47056 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46886 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46886
    | (have j0 := eq46886 X0
       grind)
    | exact resolve eq46886 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46886
  have eq47058 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq46884 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46884
    | (have j0 := eq46884 X0 X1
       grind)
    | exact resolve eq46884 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46884
  have eq47127 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47002 eq837
    | (have j0 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq47002 (M.op x y)
       grind)
    | exact resolve eq837 eq47002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47196 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq47127
  have eq47363 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47196 eq697
    | exact resolve eq697 eq47196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47367 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47196 eq706
    | exact resolve eq706 eq47196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47379 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47196 eq47367
    | exact resolve eq47367 eq47196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47367
  have eq47382 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq728 eq47363
    | exact resolve eq47363 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47363
  have eq47399 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X0) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47196 eq47382
    | exact resolve eq47382 eq47196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47196 eq47382
  have eq47412 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47379 eq47399
    | exact resolve eq47399 eq47379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47379 eq47399
  have eq49039 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq44536 y X0
       grind)
    | exact superpose eq44536 eq18
    | (have j1 := eq44536 y X0
       grind)
    | exact resolve eq18 eq44536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44536
  have eq49152 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49039 eq837
    | (have j0 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq49039 (M.op x y)
       grind)
    | exact resolve eq837 eq49039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49039
  have eq49221 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq49152
  have eq49391 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49221 eq697
    | exact resolve eq697 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49395 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49221 eq706
    | exact resolve eq706 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49407 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49221 eq49395
    | exact resolve eq49395 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49395
  have eq49410 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq728 eq49391
    | exact resolve eq49391 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49391
  have eq49427 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49221 eq49410
    | exact resolve eq49410 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49221 eq49410
  have eq49440 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49407 eq49427
    | exact resolve eq49427 eq49407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49427
  have eq57110 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq46362 (k X0 X0) x
       grind)
    | exact superpose eq46362 eq837
    | (have j0 := eq837 (M.op (σ x) (σ y))
       have j1 := eq46362 X0 x
       grind)
    | (have r₁ := eq837 (M.op (σ x) (σ y))
       have r₂ := eq46362 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq837 (σ x)
       have r₂ := eq46362 (σ x) x
       grind)
    | exact resolve eq837 eq46362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46362
  have eq57168 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq57110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57110
  have eq57387 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19878
       have i₂ := eq46366 (M.op sF0 x)
       grind)
    | exact superpose eq46366 eq19878
    | (have j1 := eq46366 X0
       grind)
    | exact resolve eq19878 eq46366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57403 : ∀ X0 : G, (M.op x y) = (σ x) ∨ x = (σ x) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq47412 X0
       have i₂ := eq46366 (M.op sF0 X0)
       grind)
    | exact superpose eq46366 eq47412
    | (have j1 := eq46366 X0
       grind)
    | exact resolve eq47412 eq46366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47412
  have eq57404 : ∀ X0 : G, (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq49440 X0
       have i₂ := eq46366 (M.op sF0 X0)
       grind)
    | exact superpose eq46366 eq49440
    | (have j1 := eq46366 X0
       grind)
    | exact resolve eq49440 eq46366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46366 eq49440
  have eq57449 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq57404 eq57403
    | (have j0 := eq57403 X0
       have j1 := eq57404 X0
       grind)
    | exact resolve eq57403 eq57404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57403 eq57404
  have eq57450 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq57449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57449
  have eq57459 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq57387
    | (have j0 := eq57387 X0
       grind)
    | exact resolve eq57387 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57387
  have eq57753 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57459 eq837
    | (have j0 := eq837 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq837 (M.op (σ x) (σ y))
       have r₂ := eq57459 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq837 eq57459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57459
  have eq57811 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57753
  have eq57938 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57811 eq706
    | exact resolve eq706 eq57811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57945 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57811 eq57938
    | exact resolve eq57938 eq57811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57811 eq57938
  have eq60144 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq46391 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq46391 eq26
    | (have j1 := eq46391 (σ y) X0
       grind)
    | exact resolve eq26 eq46391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46391
  have eq60244 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60144 eq837
    | (have j0 := eq837 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq837 (M.op (σ x) (σ y))
       have r₂ := eq60144 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq837 eq60144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60144
  have eq60302 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60244
  have eq60959 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60302 eq706
    | exact resolve eq706 eq60302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60966 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60302 eq60959
    | exact resolve eq60959 eq60302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60302 eq60959
  have eq62081 : (σ x) = (τ (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46596 eq19878
    | exact resolve eq19878 eq46596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19878
  have eq62096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46596 eq60966
    | exact resolve eq60966 eq46596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46596
  have eq62128 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62096
  have eq62161 : x = (k y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq62081
    | exact resolve eq62081 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62081
  have eq62424 : (σ x) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq62161
       grind)
    | exact superpose eq62161 eq41
    | exact resolve eq41 eq62161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62441 : (σ x) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62424
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62424
    | exact resolve eq62424 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62424
  have eq62449 : (σ x) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62441
    | exact resolve eq62441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62441
  have eq62487 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq62128
       grind)
    | exact superpose eq62128 eq41
    | exact resolve eq41 eq62128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq62504 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq62487
    | exact resolve eq62487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62487
  have eq62512 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62504
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62504
    | exact resolve eq62504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62504
  have eq62808 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq46698 (M.op x x)
       grind)
    | exact superpose eq46698 eq706
    | (have j1 := eq46698 X0
       grind)
    | exact resolve eq706 eq46698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62821 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq46698 eq62808
    | (have j0 := eq62808 X0
       have j1 := eq46698 X0
       grind)
    | exact resolve eq62808 eq46698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46698 eq62808
  have eq62841 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49407 eq62821
    | exact resolve eq62821 eq49407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49407 eq62821
  have eq62858 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47002 eq62841
    | (have j0 := eq62841 X0
       have j1 := eq47002 X0
       grind)
    | exact resolve eq62841 eq47002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62841
  have eq63760 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1 x
       have i₂ := eq47056 (M.op X0 X1)
       grind)
    | exact superpose eq47056 eq697
    | (have j1 := eq47056 X1
       grind)
    | exact resolve eq697 eq47056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63778 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq728 eq63760
    | (have j0 := eq63760 X0 X1
       grind)
    | exact resolve eq63760 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63760
  have eq63791 : ∀ X0 X1 : G, x = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44512 eq63778
    | (have j0 := eq63778 X0 X1
       have j1 := eq44512 X1
       grind)
    | exact resolve eq63778 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44512 eq63778
  have eq63803 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq47002 eq63791
    | (have j0 := eq63791 X0 X1
       have j1 := eq47002 X1
       grind)
    | exact resolve eq63791 eq47002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63791
  have eq63811 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq47056 eq63803
    | (have j0 := eq63803 X0 X1
       have j1 := eq47056 X1
       grind)
    | exact resolve eq63803 eq47056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47056 eq63803
  have eq63819 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f63819_15 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
      intro X0
      grind
    have f63819_16 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
      intro X0 X1
      grind
    have f63819_26 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) := by grind
    have f63819_27 : X0 ≠ (k X0 (σ x)) := by grind
    have f63819_28 : y ≠ (M.op x y) := by grind
    have f63819_30 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 (σ x)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f63819_16 X0 X1
         grind)
      | (have r₁ := f63819_16 X0 X1
         have r₂ := f63819_28
         grind)
      | exact resolve f63819_16 f63819_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f63819_63 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have i₁ := f63819_15 (M.op x y)
         have i₂ := f63819_30 X0 (M.op x y)
         grind)
      | exact superpose f63819_30 f63819_15
      | (have j0 := f63819_15 (M.op x y)
         have j1 := f63819_30 X0 x
         grind)
      | (have r₁ := f63819_15 (M.op x y)
         have r₂ := f63819_30 X0 (M.op x y)
         grind)
      | (have r₁ := f63819_15 (σ x)
         have r₂ := f63819_30 (σ x) x
         grind)
      | exact resolve f63819_15 f63819_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f63819_70 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f63819_63 X0
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f63819_73 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f63819_70 X0
         grind)
      | (have r₁ := f63819_70 X0
         have r₂ := f63819_26
         grind)
      | exact resolve f63819_70 f63819_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f63819_79 : X0 ≠ X0 := by
      first
      | (have i₁ := f63819_27
         have i₂ := f63819_73 X0
         grind)
      | exact superpose f63819_73 f63819_27
      | (have r₁ := f63819_27
         have r₂ := f63819_73 X0
         grind)
      | exact resolve f63819_27 f63819_73
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f63819_80 : False := by grind
    exact f63819_80
  clear eq47058
  have eq63888 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq63819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63819
  have eq67518 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq57168 (M.op x x)
       grind)
    | exact superpose eq57168 eq706
    | (have j1 := eq57168 X0
       grind)
    | exact resolve eq706 eq57168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67526 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq57168 eq67518
    | (have j0 := eq67518 X0
       have j1 := eq57168 X0
       grind)
    | exact resolve eq67518 eq57168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57168 eq67518
  have eq69333 : ∀ X0 : G, (σ x) = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq763 X0
       have i₂ := eq63811 X0 (M.op X0 (M.op sF0 x))
       grind)
    | exact superpose eq63811 eq763
    | (have j1 := eq63811 X0 X0
       grind)
    | exact resolve eq763 eq63811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63811
  have eq69370 : ∀ X0 : G, (σ x) = (M.op (M.op x y) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47002 eq69333
    | (have j0 := eq69333 X0
       have j1 := eq47002 X0
       grind)
    | exact resolve eq69333 eq47002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47002 eq69333
  have eq69405 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62858 eq69370
    | (have j0 := eq69370 X0
       have j1 := eq62858 X0
       grind)
    | exact resolve eq69370 eq62858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62858 eq69370
  have eq69705 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69405 eq837
    | (have j0 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq69405 (M.op x y)
       grind)
    | exact resolve eq837 eq69405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69405
  have eq69774 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq69705
  have eq70028 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69774 eq706
    | exact resolve eq706 eq69774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70043 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69774 eq70028
    | exact resolve eq70028 eq69774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69774 eq70028
  have eq71150 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq70043 eq1032
    | exact resolve eq1032 eq70043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq73622 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op x y))) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28714
       have i₂ := eq63888 (M.op sF0 sF0)
       grind)
    | exact superpose eq63888 eq28714
    | (have j1 := eq63888 X0
       grind)
    | exact resolve eq28714 eq63888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28714 eq63888
  have eq73653 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op x y))) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq73622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73622
  have eq73672 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op x y))) ∨ y = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq71150 eq73653
    | (have j1 := eq71150 (τ (M.op x y))
       grind)
    | exact resolve eq73653 eq71150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71150 eq73653
  have eq73690 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq28679 eq73672
    | (have j0 := eq73672 (M.op x y)
       grind)
    | exact resolve eq73672 eq28679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28679 eq73672
  have eq73701 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73690 X0
       have j1 := eq865 (M.op x y) X0
       grind)
    | (have r₁ := eq73690 X0
       have r₂ := eq865 (M.op x y) x
       grind)
    | (have r₁ := eq73690 (M.op x y)
       have r₂ := eq865 (M.op x y) x
       grind)
    | exact resolve eq73690 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq73690
  have eq73713 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73701 eq837
    | (have j0 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq837 (M.op x y)
       have r₂ := eq73701 (M.op x y)
       grind)
    | exact resolve eq837 eq73701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73701
  have eq73782 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq73713
  have eq73954 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73782 eq697
    | exact resolve eq697 eq73782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq73958 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73782 eq706
    | exact resolve eq706 eq73782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73973 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73782 eq73958
    | exact resolve eq73958 eq73782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73958
  have eq73976 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq728 eq73954
    | exact resolve eq73954 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq73954
  have eq73993 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73782 eq73976
    | exact resolve eq73976 eq73782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73782 eq73976
  have eq74006 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73973 eq73993
    | exact resolve eq73993 eq73973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73993
  have eq83682 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq67526 (M.op x X0)
       grind)
    | exact superpose eq67526 eq693
    | (have j1 := eq67526 X0
       grind)
    | exact resolve eq693 eq67526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq67526
  have eq102246 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57450 eq837
    | (have j0 := eq837 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq837 (M.op (σ x) (σ y))
       have r₂ := eq57450 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq837 eq57450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57450
  have eq102305 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq102246
  have eq104395 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102305 eq706
    | exact resolve eq706 eq102305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104442 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73973 eq104395
    | exact resolve eq104395 eq73973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104395
  have eq105802 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104442 eq102305
    | exact resolve eq102305 eq104442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102305 eq104442
  have eq105884 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq105802
  have eq105949 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105884 eq704
    | exact resolve eq704 eq105884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq105956 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq105884
  have eq105962 : (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73973 eq105949
    | exact resolve eq105949 eq73973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73973 eq105949
  have eq107739 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105962 eq11
    | exact resolve eq11 eq105962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105962
  have eq107790 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq107739
  have eq107811 : (M.op x y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq107790
       have r₂ := eq105956
       grind)
    | exact resolve eq107790 eq105956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105956 eq107790
  have eq108873 : (M.op x y) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107811 eq31338
    | exact resolve eq31338 eq107811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31338 eq107811
  have eq108901 : x = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq108873
  have eq109871 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq108901
       grind)
    | exact superpose eq108901 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq108901
       grind)
    | exact resolve eq28 eq108901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108901
  have eq109922 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq109871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109871
  have eq110116 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq878 x
       have i₂ := eq109922 x
       grind)
    | exact superpose eq109922 eq878
    | (have j0 := eq878 x
       grind)
    | exact resolve eq878 eq109922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq109922
  have eq110179 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq110116
  have eq110235 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110179
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq110179
    | exact resolve eq110179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110179
  have eq116332 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110235 eq706
    | exact resolve eq706 eq110235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq116372 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70043 eq116332
    | exact resolve eq116332 eq70043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70043 eq116332
  have eq116449 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116372 eq110235
    | exact resolve eq110235 eq116372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110235 eq116372
  have eq116541 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by grind
  clear eq116449
  have eq116613 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq116541 eq27
    | exact resolve eq27 eq116541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116541
  have eq116742 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq116613
       have r₂ := eq28642
       grind)
    | exact resolve eq116613 eq28642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116613
  have eq116752 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116742 eq26
    | exact resolve eq26 eq116742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq116742
  have eq117136 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74006 eq116752
    | exact resolve eq116752 eq74006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74006 eq116752
  have eq117461 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117136 eq27
    | exact resolve eq27 eq117136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117136
  have eq117563 : y = (M.op x y) := by
    first
    | (have r₁ := eq117461
       have r₂ := eq28642
       grind)
    | exact resolve eq117461 eq28642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28642 eq117461
  have eq117570 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq18
    | exact resolve eq18 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq117571 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq24
    | exact resolve eq24 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq117574 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq180
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq180
    | exact resolve eq180 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq117593 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq703
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq703
    | exact resolve eq703 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq117612 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62128
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq62128
    | exact resolve eq62128 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62128
  have eq117614 : x = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62161
       have i₂ := eq117563
       grind)
    | exact superpose eq117563 eq62161
    | exact resolve eq62161 eq117563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62161 eq117563
  have eq117633 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq117571 eq20
    | exact resolve eq20 eq117571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118376 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq117570 eq694
    | exact resolve eq694 eq117570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq118482 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X3) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq117593 eq708
    | exact resolve eq708 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq118488 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq117593 eq763
    | exact resolve eq763 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq118564 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq117593 eq19823
    | exact resolve eq19823 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19823
  have eq118583 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117593 eq57945
    | exact resolve eq57945 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57945
  have eq118585 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117593 eq60966
    | exact resolve eq60966 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60966
  have eq118733 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq118488 eq118482
    | exact resolve eq118482 eq118488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118482 eq118488
  have eq120165 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq118564
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq118564
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq118564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120334 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq120165
  have eq120479 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42 eq120334
    | exact resolve eq120334 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq120334
  have eq120617 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq117633 eq120479
    | exact resolve eq120479 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120479
  have eq120708 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq120617
    | exact resolve eq120617 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120617
  have eq120769 : (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq117633 eq120708
    | exact resolve eq120708 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120708
  have eq128917 : (σ x) = (k (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq120769 eq62449
    | exact resolve eq62449 eq120769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62449 eq120769
  have eq128959 : x = (σ x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq117614 eq128917
    | exact resolve eq128917 eq117614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117614 eq128917
  have eq128960 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq128959
  have eq129058 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq128960 eq118583
    | exact resolve eq118583 eq128960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118583 eq128960
  have eq129117 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq129058
  have eq129166 : (σ (M.op x y)) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq129117 eq27
    | exact resolve eq27 eq129117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129117
  have eq129188 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have r₁ := eq129166
       have r₂ := eq117633
       grind)
    | exact resolve eq129166 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129166
  have eq129201 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq129188 eq27
    | exact resolve eq27 eq129188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129221 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq129188 eq40162
    | exact resolve eq40162 eq129188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40162 eq129188
  have eq129294 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq129221
  have eq129305 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq129294
    | exact resolve eq129294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129294
  have eq129315 : (M.op x y) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq117633 eq129201
    | exact resolve eq129201 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129201
  have eq129317 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have r₁ := eq129305
       have r₂ := eq32846
       grind)
    | exact resolve eq129305 eq32846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32846 eq129305
  have eq129325 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq117633 eq129317
    | exact resolve eq129317 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129317
  have eq129331 : x = (σ x) := by
    first
    | (have r₁ := eq129325
       have r₂ := eq129315
       grind)
    | exact resolve eq129325 eq129315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129315 eq129325
  have eq129334 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq129331
       grind)
    | exact superpose eq129331 eq22
    | exact resolve eq22 eq129331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq129578 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq117570
       have i₂ := eq129331
       grind)
    | exact superpose eq129331 eq117570
    | exact resolve eq117570 eq129331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139372 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117612 eq810
    | (have j0 := eq810 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq810 eq117612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq117612
  have eq139653 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139372
  have eq139739 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117570 eq139653
    | exact resolve eq139653 eq117570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117570 eq139653
  have eq139923 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117593 eq139739
    | exact resolve eq139739 eq117593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117593 eq139739
  have eq139924 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139923
  have eq140741 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139924 eq117574
    | exact resolve eq117574 eq139924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117574
  have eq140746 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139924 eq118564
    | exact resolve eq118564 eq139924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118564
  have eq140752 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139924 eq118585
    | exact resolve eq118585 eq139924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118585 eq139924
  have eq140807 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq140752
  have eq140825 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq140746
    | exact resolve eq140746 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140746
  have eq140826 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq140741
    | exact resolve eq140741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq140741
  have eq140835 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117633 eq140825
    | exact resolve eq140825 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140825
  have eq140836 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117633 eq140826
    | exact resolve eq140826 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140826
  have eq140842 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62512 eq140836
    | exact resolve eq140836 eq62512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62512 eq140836
  have eq140847 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140835 eq140842
    | exact resolve eq140842 eq140835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140835 eq140842
  have eq140850 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140807 eq27
    | exact resolve eq27 eq140807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140807
  have eq140874 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140850
       have r₂ := eq117633
       grind)
    | exact resolve eq140850 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140850
  have eq140888 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140874 eq27
    | exact resolve eq27 eq140874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140943 : ∀ X0 : G, (σ x) = (M.op x (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq140874 eq83682
    | (have j0 := eq83682 X0
       grind)
    | exact resolve eq83682 eq140874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83682
  have eq140959 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140874 eq118376
    | exact resolve eq118376 eq140874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118376
  have eq140972 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq140874
  have eq140986 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq140943 X0
       have i₂ := eq129331
       grind)
    | exact superpose eq129331 eq140943
    | (have j0 := eq140943 X0
       grind)
    | exact resolve eq140943 eq129331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129331 eq140943
  have eq141002 : (σ x) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117633 eq140888
    | exact resolve eq140888 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140888
  have eq141008 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq140986 X0
       have j1 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq140986 X0
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq140986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq140986
  have eq141014 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq141008 X0
       grind)
    | (have r₁ := eq141008 X0
       have r₂ := eq141002
       grind)
    | exact resolve eq141008 eq141002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141002 eq141008
  have eq141039 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141014 eq837
    | (have j0 := eq837 (σ x)
       grind)
    | (have r₁ := eq837 (σ x)
       have r₂ := eq141014 (σ x)
       grind)
    | exact resolve eq837 eq141014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq141014
  have eq141144 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq141039
  have eq142225 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140847 eq27
    | exact resolve eq27 eq140847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140847
  have eq142262 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq142225
       have r₂ := eq117633
       grind)
    | exact resolve eq142225 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142225
  have eq144360 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140959 eq141144
    | exact resolve eq141144 eq140959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140959 eq141144
  have eq144428 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq144360
  have eq144671 : (σ x) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq144428 eq118733
    | exact resolve eq118733 eq144428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118733 eq144428
  have eq144695 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq129578 eq144671
    | exact resolve eq144671 eq129578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129578 eq144671
  have eq144720 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq144695
       have r₂ := eq140972
       grind)
    | exact resolve eq144695 eq140972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140972 eq144695
  have eq144749 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq144720 eq27
    | exact resolve eq27 eq144720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq144844 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq144720 eq142262
    | exact resolve eq142262 eq144720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142262 eq144720
  have eq144845 : (M.op x y) = (σ x) := by grind
  clear eq144844
  have eq144868 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq117633 eq144749
    | exact resolve eq144749 eq117633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117633 eq144749
  have eq145130 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq144845 eq129334
    | exact resolve eq129334 eq144845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129334 eq144845
  have eq146099 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq145130 eq117571
    | exact resolve eq117571 eq145130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117571 eq145130
  have eq146411 : False := by grind
  exact eq146411

/-- `Equation4467`: `x ◇ (y ◇ x) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4467 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4467 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4467.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq207
  have eq689 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x X2) X4 X5
       have i₂ := eq16 X0 X1 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq692 x x X2 X3 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq698 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq689 x x X2 X4 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq689
    | exact resolve eq689 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq699 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq696 x x X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq696
    | exact resolve eq696 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 (M.op X0 X1) X1
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op x y) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq693 X2 (M.op x X2)
       have i₂ := eq16 X0 X1 x X2
       grind)
    | exact superpose eq16 eq693
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 (σ y) (σ x)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq702 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq702
    | exact resolve eq702 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq716 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op x y) y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq704 eq16
    | exact resolve eq16 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq717 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq716 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq716
    | exact resolve eq716 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq728 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq751 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq728 eq699
    | exact resolve eq699 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq699 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq699 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq770 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq728 eq765
    | exact resolve eq765 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq775 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq770 eq35
    | exact resolve eq35 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq788 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq775 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq801 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq840 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq850 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq810
    | (have j0 := eq810 X0 X1 x x
       grind)
    | exact resolve eq810 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq854 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq805
    | (have j0 := eq805 X1 X1 x x
       grind)
    | exact resolve eq805 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq805
  have eq856 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq865 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op (M.op x y) y) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | exact superpose eq728 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq866 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq728 eq854
    | (have j0 := eq854 X1 X1
       grind)
    | exact resolve eq854 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq869 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq829 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq829
    | (have j0 := eq829 (σ X0)
       grind)
    | exact resolve eq829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq788 eq829
    | (have j0 := eq829 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq829 (σ (M.op (M.op x y) y))
       have r₂ := eq788 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq829 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq902
  have eq2920 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq814
       grind)
    | exact superpose eq814 eq40
    | exact resolve eq40 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2921 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2920
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2920
    | exact resolve eq2920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920
  have eq2923 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2921
    | exact resolve eq2921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq5519 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 (M.op X0 X1)) = X2 ∨ (M.op (M.op x y) y) = (k X1 (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (M.op X0 X1)
       have i₂ := eq865 X1 X0
       grind)
    | exact superpose eq865 eq28
    | (have j0 := eq28 X2 (M.op X0 X1)
       have j1 := eq865 X1 X0
       grind)
    | (have r₁ := eq28 X0 (M.op X1 X0)
       have r₂ := eq865 X0 X1
       grind)
    | exact resolve eq28 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq5540 : ∀ X0 X1 X2 : G, (M.op (M.op x y) y) = (k X1 (M.op X0 X1)) ∨ (k X2 (M.op X0 X1)) = X2 ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5519 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq21140 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq915 eq706
    | exact resolve eq706 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21141 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq915 eq708
    | exact resolve eq708 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq21148 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq915 eq21141
    | exact resolve eq21141 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq21141
  have eq21163 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq700 eq21148
    | exact resolve eq21148 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq21148
  have eq21219 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq21163 eq15
    | exact resolve eq15 eq21163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2923 eq821
    | exact resolve eq821 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23736 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23728
       have r₂ := eq27
       grind)
    | exact resolve eq23728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728
  have eq23743 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23736 eq218
    | exact resolve eq218 eq23736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23736
  have eq23781 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq23743
    | exact resolve eq23743 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23743
  have eq23794 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq23781
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq23781
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq23781
       have r₂ := eq13 y x
       grind)
    | exact resolve eq23781 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23781
  have eq23798 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq23794
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq23794
       have r₂ := eq28 x x
       grind)
    | exact resolve eq23794 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23794
  have eq23800 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq23798 eq200
    | exact resolve eq200 eq23798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23798
  have eq23837 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq23800
    | exact resolve eq23800 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23800
  have eq23850 : y = (k y x) := by
    first
    | (have j1 := eq856 x y
       grind)
    | (have r₁ := eq23837
       have r₂ := eq856 x x
       grind)
    | exact resolve eq23837 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq23837
  have eq23859 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq814
       have i₂ := eq23850
       grind)
    | exact superpose eq23850 eq814
    | exact resolve eq814 eq23850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq23861 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq23850
       grind)
    | exact superpose eq23850 eq40
    | exact resolve eq40 eq23850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq23850
  have eq23863 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq23861
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23861
    | exact resolve eq23861 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23861
  have eq23870 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23863 eq2923
    | exact resolve eq2923 eq23863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq23873 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23863 eq821
    | exact resolve eq821 eq23863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq23863
  have eq24002 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23859
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq23859
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq23859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24007 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq23859
       grind)
    | exact superpose eq23859 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq23859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24021 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23859
       grind)
    | exact superpose eq23859 eq706
    | exact resolve eq706 eq23859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23859
  have eq24024 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq24007
  have eq24025 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq24002
  have eq24028 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24021
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24021
    | exact resolve eq24021 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24021
  have eq24041 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24024 eq24025
    | exact resolve eq24025 eq24024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024 eq24025
  have eq24042 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq24041
  have eq24075 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23870
       grind)
    | exact superpose eq23870 eq706
    | exact resolve eq706 eq23870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23870
  have eq24082 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24075
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24075
    | exact resolve eq24075 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24075
  have eq24110 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23873
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq23873
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq23873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24115 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23873 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq23873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24129 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23873 eq706
    | exact resolve eq706 eq23873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23873
  have eq24132 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24115
  have eq24133 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq24110
  have eq24136 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24129
    | exact resolve eq24129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24129
  have eq24149 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24132 eq24133
    | exact resolve eq24133 eq24132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24132 eq24133
  have eq24150 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24149
  have eq24176 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24028 eq770
    | exact resolve eq770 eq24028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24249 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24028 eq21163
    | exact resolve eq21163 eq24028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24028
  have eq24281 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq24249
    | exact resolve eq24249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24249
  have eq24911 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq24281
       grind)
    | exact superpose eq24281 eq706
    | exact resolve eq706 eq24281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24918 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24281 eq24911
    | exact resolve eq24911 eq24281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24281 eq24911
  have eq25181 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24918 eq21163
    | exact resolve eq21163 eq24918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25199 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24918 eq706
    | exact resolve eq706 eq24918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24918
  have eq25209 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25199
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25199
    | exact resolve eq25199 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25199
  have eq25221 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25181
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25181
    | exact resolve eq25181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25181
  have eq25299 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25209 eq25221
    | exact resolve eq25221 eq25209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25221
  have eq25351 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25209 eq29
    | exact resolve eq29 eq25209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq25465 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25299 eq30
    | exact resolve eq30 eq25299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25299
  have eq25585 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25209 eq25465
    | exact resolve eq25465 eq25209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25209 eq25465
  have eq25903 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25585 eq14
    | exact resolve eq14 eq25585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25585
  have eq25977 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25903
    | exact resolve eq25903 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25903
  have eq25978 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq25977
  have eq28694 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq24042
       grind)
    | exact superpose eq24042 eq41
    | exact resolve eq41 eq24042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq24042
  have eq28712 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28694
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28694
    | exact resolve eq28694 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28694
  have eq28719 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28712
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28712
    | exact resolve eq28712 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28712
  have eq28737 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq24082 eq770
    | exact resolve eq770 eq24082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28810 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24082 eq21163
    | exact resolve eq21163 eq24082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24082
  have eq28845 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq28810
    | exact resolve eq28810 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28810
  have eq29152 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5540 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5540
    | (have j0 := eq5540 x y X0
       grind)
    | exact resolve eq5540 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540
  have eq30162 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq28845
       grind)
    | exact superpose eq28845 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq28845
       grind)
    | exact resolve eq28 eq28845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30177 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq28845
       grind)
    | exact superpose eq28845 eq706
    | exact resolve eq706 eq28845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30180 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq30162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30162
  have eq30184 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25978 eq30177
    | exact resolve eq30177 eq25978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30177
  have eq30199 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28845 eq30184
    | exact resolve eq30184 eq28845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28845 eq30184
  have eq30233 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq869 x
       have i₂ := eq30180 x
       grind)
    | exact superpose eq30180 eq869
    | (have j0 := eq869 x
       grind)
    | exact resolve eq869 eq30180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30180
  have eq30292 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq30233
  have eq30342 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq30292
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30292
    | exact resolve eq30292 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30292
  have eq30697 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30342 eq706
    | exact resolve eq706 eq30342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30705 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25978 eq30697
    | exact resolve eq30697 eq25978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30697
  have eq30719 : x = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30199 eq30705
    | exact resolve eq30705 eq30199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30199 eq30705
  have eq30732 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30342 eq30719
    | exact resolve eq30719 eq30342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30342 eq30719
  have eq30823 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  have eq33193 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24136 eq770
    | exact resolve eq770 eq24136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq33266 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24136 eq21163
    | exact resolve eq21163 eq24136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24136
  have eq33618 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33266 eq706
    | exact resolve eq706 eq33266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33625 : (σ x) = (M.op (M.op x y) y) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33266 eq33618
    | exact resolve eq33618 eq33266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33266 eq33618
  have eq34067 : (σ x) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33625 eq21219
    | exact resolve eq21219 eq33625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33625
  have eq34112 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq34067
    | exact resolve eq34067 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34067
  have eq37212 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24150 eq116
    | exact resolve eq116 eq24150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq37237 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq37212
    | exact resolve eq37212 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37212
  have eq37755 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq24176 X0
       grind)
    | exact superpose eq24176 eq706
    | (have j1 := eq24176 X0
       grind)
    | exact resolve eq706 eq24176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37762 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24176 eq37755
    | (have j0 := eq37755 X0
       have j1 := eq24176 X0
       grind)
    | exact resolve eq37755 eq24176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24176 eq37755
  have eq39045 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq28737 X0
       grind)
    | exact superpose eq28737 eq706
    | (have j1 := eq28737 X0
       grind)
    | exact resolve eq706 eq28737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39054 : ∀ X0 : G, x = (M.op (M.op x y) y) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq28737 eq39045
    | (have j0 := eq39045 X0
       have j1 := eq28737 X0
       grind)
    | exact resolve eq39045 eq28737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28737 eq39045
  have eq39595 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq33193 (M.op X1 X1)
       grind)
    | exact superpose eq33193 eq28
    | (have j0 := eq28 X0 (σ x)
       have j1 := eq33193 X1
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq33193 X0
       grind)
    | exact resolve eq28 eq33193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39610 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq33193 (M.op x x)
       grind)
    | exact superpose eq33193 eq706
    | (have j1 := eq33193 X0
       grind)
    | exact resolve eq706 eq33193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39615 : ∀ X0 X1 : G, (k X1 (M.op (σ x) (σ y))) = X1 ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq39595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39595
  have eq39619 : ∀ X0 : G, (σ x) = (M.op (M.op x y) y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33193 eq39610
    | (have j0 := eq39610 X0
       have j1 := eq33193 X0
       grind)
    | exact resolve eq39610 eq33193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33193 eq39610
  have eq40843 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37237 eq706
    | exact resolve eq706 eq37237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40852 : (σ x) = (M.op (M.op x y) y) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37237 eq40843
    | exact resolve eq40843 eq37237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37237 eq40843
  have eq41195 : ∀ X0 : G, x = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21140
       have i₂ := eq37762 (M.op sF0 y)
       grind)
    | exact superpose eq37762 eq21140
    | (have j1 := eq37762 X0
       grind)
    | exact resolve eq21140 eq37762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140
  have eq41196 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21163
       have i₂ := eq37762 (M.op sF0 y)
       grind)
    | exact superpose eq37762 eq21163
    | (have j1 := eq37762 X0
       grind)
    | exact resolve eq21163 eq37762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21163
  have eq41222 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq37762 (M.op x x)
       grind)
    | exact superpose eq37762 eq706
    | (have j1 := eq37762 X0
       grind)
    | exact resolve eq706 eq37762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37762
  have eq41244 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq41222 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41222
    | (have j0 := eq41222 X0
       grind)
    | exact resolve eq41222 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41222
  have eq41257 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq41196 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41196
    | (have j0 := eq41196 X0
       grind)
    | exact resolve eq41196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41196
  have eq41258 : ∀ X0 : G, x = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq41195 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41195
    | (have j0 := eq41195 X0
       grind)
    | exact resolve eq41195 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41195
  have eq41337 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41244 eq41257
    | (have j0 := eq41257 X0
       have j1 := eq41244 X0
       grind)
    | exact resolve eq41257 eq41244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41257
  have eq41338 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41244 eq41258
    | (have j0 := eq41258 X0
       have j1 := eq41244 X0
       grind)
    | exact resolve eq41258 eq41244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41244 eq41258
  have eq41365 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41337 eq41338
    | (have j0 := eq41338 X0
       have j1 := eq41337 X0
       grind)
    | exact resolve eq41338 eq41337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41337 eq41338
  have eq41377 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq41365 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq41365 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq41365 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41365
  have eq41388 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41377 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq41377 (M.op x y)
       grind)
    | exact resolve eq829 eq41377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41458 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq41388
  have eq41627 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41458 eq706
    | exact resolve eq706 eq41458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41641 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41458 eq41627
    | exact resolve eq41627 eq41458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41458 eq41627
  have eq41697 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41641 eq751
    | exact resolve eq751 eq41641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47206 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq698 x x x
       have i₂ := eq39054 (M.op x x)
       grind)
    | exact superpose eq39054 eq698
    | (have j1 := eq39054 X1
       grind)
    | exact resolve eq698 eq39054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq39054
  have eq47236 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq710 eq47206
    | (have j0 := eq47206 x X1
       grind)
    | exact resolve eq47206 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq47206
  have eq47322 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq47236 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47236
    | (have j0 := eq47236 X1
       grind)
    | exact resolve eq47236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47236
  have eq47362 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq41377 eq47322
    | (have j0 := eq47322 X1
       have j1 := eq41377 X1
       grind)
    | exact resolve eq47322 eq41377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47322
  have eq47388 : ∀ X1 : G, (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have j0 := eq47362 X1
       have j1 := eq28 X1 (M.op x y)
       grind)
    | (have r₁ := eq47362 X1
       have r₂ := eq28 x (M.op x y)
       grind)
    | exact resolve eq47362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47362
  have eq47412 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47388 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq47388 (M.op x y)
       grind)
    | exact resolve eq829 eq47388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47388 eq869
    | (have j0 := eq869 (M.op x y)
       grind)
    | exact resolve eq869 eq47388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47480 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq47416
  have eq47482 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq47412
  have eq47539 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq47480
    | exact resolve eq47480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47480
  have eq47608 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47482 eq706
    | exact resolve eq706 eq47482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47629 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47482 eq47608
    | exact resolve eq47608 eq47482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47482 eq47608
  have eq47913 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47539 eq706
    | exact resolve eq706 eq47539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47933 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47539 eq47913
    | exact resolve eq47913 eq47539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47539 eq47913
  have eq47948 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47629 eq47933
    | exact resolve eq47933 eq47629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47629 eq47933
  have eq48043 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq52329 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq829 X0
       have i₂ := eq39615 (k X0 X0) x
       grind)
    | exact superpose eq39615 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       have j1 := eq39615 X0 x
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq39615 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (σ x)
       have r₂ := eq39615 (σ x) x
       grind)
    | exact resolve eq829 eq39615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39615
  have eq52392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq52329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52329
  have eq52598 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21219
       have i₂ := eq39619 (M.op sF0 y)
       grind)
    | exact superpose eq39619 eq21219
    | (have j1 := eq39619 X0
       grind)
    | exact resolve eq21219 eq39619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39619
  have eq52664 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq52598
    | (have j0 := eq52598 X0
       grind)
    | exact resolve eq52598 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52598
  have eq52950 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52664 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq52664 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq829 eq52664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52664
  have eq53013 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52950
  have eq53138 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53013 eq706
    | exact resolve eq706 eq53013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53155 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53013 eq53138
    | exact resolve eq53138 eq53013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53013 eq53138
  have eq56782 : (σ x) = (τ (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40852 eq21219
    | exact resolve eq21219 eq40852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40852
  have eq56854 : x = (k y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq56782
    | exact resolve eq56782 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56782
  have eq57126 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq866 y y
       have i₂ := eq56854
       grind)
    | exact superpose eq56854 eq866
    | (have j0 := eq866 y y
       grind)
    | exact resolve eq866 eq56854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq56854
  have eq57127 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57126
  have eq57131 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57127
    | exact resolve eq57127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57127
  have eq57143 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41641 eq57131
    | exact resolve eq57131 eq41641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57131
  have eq57152 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41697 eq57143
    | (have j1 := eq41697 (M.op x y)
       grind)
    | exact resolve eq57143 eq41697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57143
  have eq57153 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57152
  have eq57223 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57153 eq706
    | exact resolve eq706 eq57153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57240 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53155 eq57223
    | exact resolve eq57223 eq53155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53155 eq57223
  have eq57256 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57153 eq57240
    | exact resolve eq57240 eq57153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57153 eq57240
  have eq57283 : (σ (M.op x y)) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57256 eq27
    | exact resolve eq27 eq57256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57256
  have eq57305 : (σ y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30732 eq57283
    | (have r₁ := eq57283
       have r₂ := eq30732
       grind)
    | exact resolve eq57283 eq30732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30732 eq57283
  have eq57308 : (σ y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq57305
  have eq57309 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq57308
  have eq57336 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq57309 eq34112
    | exact resolve eq34112 eq57309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34112 eq57309
  have eq57376 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq57336
  have eq57402 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq57376
       have r₂ := eq30823
       grind)
    | exact resolve eq57376 eq30823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30823 eq57376
  have eq57434 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq57402
    | exact resolve eq57402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57402
  have eq57435 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq57434
  have eq62975 : ∀ X0 X1 : G, (k X0 (σ (k y (M.op x y)))) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq788 X0
       have i₂ := eq29152 (M.op sF0 y)
       grind)
    | exact superpose eq29152 eq788
    | (have j1 := eq29152 X1
       grind)
    | exact resolve eq788 eq29152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq29152
  have eq63196 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ (M.op x y)))) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq42 eq62975
    | (have j0 := eq62975 X0 X1
       grind)
    | exact resolve eq62975 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq62975
  have eq63317 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ (M.op x y)))) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq63196 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63196
    | (have j0 := eq63196 X0 X1
       grind)
    | exact resolve eq63196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63196
  have eq63428 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ (M.op x y)))) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq41377 eq63317
    | (have j0 := eq63317 X0 X1
       have j1 := eq41377 X1
       grind)
    | exact resolve eq63317 eq41377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41377 eq63317
  have eq63523 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ (M.op x y)))) = X0 ∨ (k X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63428 X0 X1
       have j1 := eq28 X0 (k (σ y) (σ (M.op x y)))
       grind)
    | (have r₁ := eq63428 X0 X1
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq63428 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63428
  have eq63600 : ∀ X0 X1 : G, (k X0 (k (σ y) (σ y))) = X0 ∨ (k X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq47388 eq63523
    | (have j0 := eq63523 X0 X1
       have j1 := eq47388 X1
       grind)
    | exact resolve eq63523 eq47388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47388 eq63523
  have eq64348 : ∀ X0 X1 : G, (k X0 (σ x)) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24150 eq63600
    | (have j0 := eq63600 X0 X1
       grind)
    | exact resolve eq63600 eq24150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24150 eq63600
  have eq64459 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq64348 X0 X1
       have j1 := eq28 X1 (M.op x y)
       grind)
    | (have r₁ := eq64348 X0 X1
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq64348 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq64348
  have eq68047 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq64459 (k X0 X0) x
       grind)
    | exact superpose eq64459 eq869
    | (have j0 := eq869 (M.op x y)
       have j1 := eq64459 X0 x
       grind)
    | exact resolve eq869 eq64459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq64459
  have eq68122 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq68047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68047
  have eq68181 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq68122
    | (have j0 := eq68122 X0
       grind)
    | exact resolve eq68122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68122
  have eq70450 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq68181 (M.op x x)
       grind)
    | exact superpose eq68181 eq706
    | (have j1 := eq68181 X0
       grind)
    | exact resolve eq706 eq68181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70470 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq68181 eq70450
    | (have j0 := eq70450 X0
       have j1 := eq68181 X0
       grind)
    | exact resolve eq70450 eq68181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68181 eq70450
  have eq73871 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq706 x x
       have i₂ := eq52392 (M.op x x)
       grind)
    | exact superpose eq52392 eq706
    | (have j1 := eq52392 X0
       grind)
    | exact resolve eq706 eq52392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73889 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq52392 eq73871
    | (have j0 := eq73871 X0
       have j1 := eq52392 X0
       grind)
    | exact resolve eq73871 eq52392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52392 eq73871
  have eq73903 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq70470 eq73889
    | (have j0 := eq73889 X0
       have j1 := eq70470 X0
       grind)
    | exact resolve eq73889 eq70470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70470 eq73889
  have eq73915 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq73903 X0
       grind)
    | (have r₁ := eq73903 X0
       have r₂ := eq27
       grind)
    | exact resolve eq73903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73903
  have eq73932 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73915 eq829
    | (have j0 := eq829 (σ x)
       grind)
    | (have r₁ := eq829 (σ x)
       have r₂ := eq73915 (σ x)
       grind)
    | exact resolve eq829 eq73915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq73915
  have eq74026 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq73932
  have eq74159 : (M.op (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74026 eq706
    | exact resolve eq706 eq74026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74178 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74026 eq74159
    | exact resolve eq74159 eq74026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74026 eq74159
  have eq74478 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq74178 eq751
    | exact resolve eq751 eq74178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74556 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74178 eq21219
    | exact resolve eq21219 eq74178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21219
  have eq74576 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq74178 eq41697
    | exact resolve eq41697 eq74178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41697 eq74178
  have eq74640 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq30 eq74556
    | exact resolve eq74556 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74556
  have eq74842 : (σ (M.op x y)) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq74640 eq27
    | exact resolve eq27 eq74640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74640
  have eq74865 : (M.op x y) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq57435 eq74842
    | exact resolve eq74842 eq57435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74842
  have eq75400 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74478 eq26
    | (have j1 := eq74478 (σ y)
       grind)
    | exact resolve eq26 eq74478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74478
  have eq75522 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75400 eq27
    | exact resolve eq27 eq75400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75400
  have eq75549 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47948 eq75522
    | (have r₁ := eq75522
       have r₂ := eq47948
       grind)
    | exact resolve eq75522 eq47948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75554 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq75549
  have eq75563 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq75554 eq27
    | exact resolve eq27 eq75554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75554
  have eq75663 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47948 eq75563
    | exact resolve eq75563 eq47948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75665 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq75663
       have r₂ := eq48043
       grind)
    | exact resolve eq75663 eq48043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48043 eq75663
  have eq78845 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq74576 eq27
    | exact resolve eq27 eq74576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78852 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq74576 eq728
    | exact resolve eq728 eq74576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq74576
  have eq78865 : (M.op x y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq41641 eq78852
    | exact resolve eq78852 eq41641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78852
  have eq78870 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq25978 eq78845
    | exact resolve eq78845 eq25978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25978 eq78845
  have eq82305 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq78865 eq11
    | exact resolve eq11 eq78865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78865
  have eq82344 : (M.op x y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by grind
  clear eq82305
  have eq82365 : (M.op x y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq82344
       have r₂ := eq78870
       grind)
    | exact resolve eq82344 eq78870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78870 eq82344
  have eq83241 : (M.op x y) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq82365 eq28719
    | exact resolve eq28719 eq82365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28719 eq82365
  have eq83268 : x = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq83241
  have eq83946 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq83268
       grind)
    | exact superpose eq83268 eq706
    | exact resolve eq706 eq83268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83974 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83268 eq83946
    | exact resolve eq83946 eq83268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83268 eq83946
  have eq83989 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41641 eq83974
    | exact resolve eq83974 eq41641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41641 eq83974
  have eq84017 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83989 eq30
    | exact resolve eq30 eq83989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq83989
  have eq84296 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25351 eq84017
    | exact resolve eq84017 eq25351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25351 eq84017
  have eq84297 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq84296
  have eq84361 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq84297
       grind)
    | exact superpose eq84297 eq24
    | exact resolve eq24 eq84297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq84619 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq84361
    | exact resolve eq84361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84361
  have eq84849 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84619 eq57435
    | exact resolve eq57435 eq84619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57435
  have eq84857 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84619 eq75522
    | (have r₁ := eq75522
       have r₂ := eq84619
       grind)
    | exact resolve eq75522 eq84619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75522 eq84619
  have eq84859 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq84857
  have eq84863 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq84849
       have r₂ := eq74865
       grind)
    | exact resolve eq84849 eq74865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74865 eq84849
  have eq84934 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84859 eq699
    | exact resolve eq699 eq84859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq85005 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq84934
    | (have j0 := eq84934 X0
       grind)
    | exact resolve eq84934 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84934
  have eq85013 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84859 eq85005
    | exact resolve eq85005 eq84859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84859 eq85005
  have eq85028 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq84863
       grind)
    | exact superpose eq84863 eq18
    | exact resolve eq18 eq84863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85128 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq84863
  have eq85146 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq84297 eq85028
    | exact resolve eq85028 eq84297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84297 eq85028
  have eq86269 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85146 eq85013
    | exact resolve eq85013 eq85146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85013 eq85146
  have eq86311 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq86269
  have eq86334 : x = (M.op x y) := by
    first
    | (have r₁ := eq86311
       have r₂ := eq85128
       grind)
    | exact resolve eq86311 eq85128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85128 eq86311
  have eq86356 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq86334
       grind)
    | exact superpose eq86334 eq18
    | exact resolve eq18 eq86334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86357 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq86334
       grind)
    | exact superpose eq86334 eq22
    | exact resolve eq22 eq86334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq86334
  have eq86471 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86357 eq20
    | exact resolve eq20 eq86357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq86357
  have eq86843 : (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47948 eq86471
    | exact resolve eq86471 eq47948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47948
  have eq86950 : (σ x) ≠ (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq86471 eq75563
    | (have r₁ := eq75563
       have r₂ := eq86471
       grind)
    | exact resolve eq75563 eq86471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75563 eq86471
  have eq86954 : (M.op x y) = (σ x) := by grind
  clear eq86950
  have eq87019 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq86843
       have r₂ := eq75665
       grind)
    | exact resolve eq86843 eq75665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75665 eq86843
  have eq87139 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq86954 eq26
    | exact resolve eq26 eq86954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq86954
  have eq90404 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq86356 eq717
    | exact resolve eq717 eq86356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq90407 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq86356 eq751
    | exact resolve eq751 eq86356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq90611 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq90407 eq90404
    | exact resolve eq90404 eq90407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90404 eq90407
  have eq92267 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq90611 eq706
    | exact resolve eq706 eq90611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq90611
  have eq92290 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq87139 eq92267
    | exact resolve eq92267 eq87139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87139 eq92267
  have eq92306 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86356 eq92290
    | exact resolve eq92290 eq86356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86356 eq92290
  have eq92323 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq92306 eq27
    | exact resolve eq27 eq92306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq92306
  have eq92395 : False := by grind
  exact eq92395

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq49 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X1) X1) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op x (M.op X1 X1)) X1 X3
       have i₂ := eq14 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    grind
  have eq60 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq64 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq167 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq167
  have eq209 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq52 x
       have i₂ := eq14 x y X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : (M.op (M.op y y) (M.op y y)) = (k (M.op (M.op y y) (M.op y y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq56 x (M.op y y)
       have i₂ := eq52 (M.op x (M.op y y))
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq645 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq53 eq640
    | exact resolve eq640 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq640
  have eq647 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq638
       have i₂ := eq52 (M.op y y)
       grind)
    | exact superpose eq52 eq638
    | exact resolve eq638 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq638
  have eq1374 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1375 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq8929 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq647 eq1375
    | (have j0 := eq1375 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1375 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq8934 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1375 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1375
    | (have j0 := eq1375 (τ X0)
       grind)
    | exact resolve eq1375 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1375
  have eq8939 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq8929
  have eq8946 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8934 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8934
    | (have j0 := eq8934 X0
       grind)
    | exact resolve eq8934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq8952 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8946 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8946
    | (have j0 := eq8946 X0
       grind)
    | exact resolve eq8946 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq22599 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) = (M.op X0 (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y)))) := by
    intro X0
    first
    | exact superpose eq8939 eq49
    | exact resolve eq49 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq22633 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (M.op X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq8939 eq22599
    | exact resolve eq22599 eq8939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8939 eq22599
  have eq23428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq23429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23428
    | exact resolve eq23428 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23428
  have eq23440 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23429
       have r₂ := eq28
       grind)
    | exact resolve eq23429 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23429
  have eq23447 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq23440
  have eq23546 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23447 eq108
    | exact resolve eq108 eq23447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23447
  have eq23581 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq23546
    | exact resolve eq23546 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546
  have eq23584 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq8952 y
       grind)
    | (have r₁ := eq23581
       have r₂ := eq8952 y
       grind)
    | exact resolve eq23581 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952 eq23581
  have eq23588 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq23584
  have eq23675 : (τ (σ x)) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23588 eq64
    | exact resolve eq64 eq23588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq23588
  have eq23692 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq23675
    | exact resolve eq23675 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23675
  have eq23695 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq23692
       have r₂ := eq12 x y
       grind)
    | exact resolve eq23692 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23692
  have eq23699 : x = (k x y) ∨ x = (k x y) := by grind
  clear eq23695
  have eq23759 : x = (k x y) := by grind
  clear eq23699
  have eq23784 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23759
       grind)
    | exact superpose eq23759 eq45
    | exact resolve eq45 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq23793 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq23759
       grind)
    | exact superpose eq23759 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq23759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23759
  have eq23794 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23793
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23793
    | exact resolve eq23793 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23793
  have eq23803 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23784
    | exact resolve eq23784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23784
  have eq23817 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23803 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq23803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23803
  have eq23818 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq23817
    | exact resolve eq23817 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23817
  have eq23981 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 y x
       have i₂ := eq23794
       grind)
    | exact superpose eq23794 eq54
    | exact resolve eq54 eq23794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24520 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq24525 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq23818 eq54
    | exact resolve eq54 eq23818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25054 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24520 eq108
    | exact resolve eq108 eq24520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq24520
  have eq25087 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq30 eq25054
    | exact resolve eq25054 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25054
  have eq25274 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq25087 eq14
    | exact resolve eq14 eq25087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25087
  have eq45545 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23981 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23981
    | (have j0 := eq23981 x X0
       grind)
    | exact resolve eq23981 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45926 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23794
       have i₂ := eq23981 y X0
       grind)
    | (have i₁ := eq23794
       have i₂ := eq23981 X0 y
       grind)
    | exact superpose eq23981 eq23794
    | exact resolve eq23794 eq23981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23981
  have eq45949 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq45926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45926
  have eq46420 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23794
       have i₂ := eq45545 y
       grind)
    | exact superpose eq45545 eq23794
    | exact resolve eq23794 eq45545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23794 eq45545
  have eq46443 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq46420
  have eq46615 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq46443
       grind)
    | exact superpose eq46443 eq14
    | exact resolve eq14 eq46443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46621 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 x x
       have i₂ := eq46443
       grind)
    | exact superpose eq46443 eq54
    | exact resolve eq54 eq46443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46443
  have eq46757 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq45949 X0
       grind)
    | exact superpose eq45949 eq54
    | (have j1 := eq45949 X2
       grind)
    | exact resolve eq54 eq45949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47653 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq46621 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq46621
    | (have j0 := eq46621 x X0
       grind)
    | exact resolve eq46621 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46621
  have eq48561 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq47653 y
       grind)
    | exact superpose eq47653 eq109
    | exact resolve eq109 eq47653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq48581 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq48561
  have eq48612 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq48581
    | exact resolve eq48581 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48581
  have eq137418 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq24525
    | (have j0 := eq24525 (σ x) X0
       grind)
    | exact resolve eq24525 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137992 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq24525 eq23818
    | exact resolve eq23818 eq24525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24525
  have eq138016 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq137992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137992
  have eq138829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq137418 eq23818
    | exact resolve eq23818 eq137418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23818 eq137418
  have eq138852 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq138829
  have eq139225 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq138852 eq54
    | exact resolve eq54 eq138852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139307 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq138852 eq14
    | exact resolve eq14 eq138852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138852
  have eq139525 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X2 (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq138016 eq54
    | (have j1 := eq138016 X2
       grind)
    | exact resolve eq54 eq138016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq138016
  have eq142480 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq139225
    | (have j0 := eq139225 (σ x) X0
       grind)
    | exact resolve eq139225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139225
  have eq143914 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq142480 eq169
    | exact resolve eq169 eq142480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq143943 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq143914
  have eq145650 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq143943
       grind)
    | exact superpose eq143943 eq93
    | exact resolve eq93 eq143943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq143943
  have eq145715 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145650
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq145650
    | exact resolve eq145650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145650
  have eq147800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq145715 eq48612
    | exact resolve eq48612 eq145715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145715
  have eq147832 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq147800
       have r₂ := eq28
       grind)
    | exact resolve eq147800 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147800
  have eq147836 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147832 eq28
    | exact resolve eq28 eq147832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147859 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq150019 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq139307 eq142480
    | (have j1 := eq139307 (σ x)
       grind)
    | exact resolve eq142480 eq139307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139307 eq142480
  have eq150295 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq150019
  have eq219241 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq46757 x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq46757
    | (have j0 := eq46757 x X0 X1
       grind)
    | exact resolve eq46757 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46757
  have eq221145 : ∀ X0 : G, y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq219241 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219241
  have eq298593 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq47653 x
       have i₂ := eq46615 x X0
       grind)
    | exact superpose eq46615 eq47653
    | (have j1 := eq46615 x X0
       grind)
    | exact resolve eq47653 eq46615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46615 eq47653
  have eq299052 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq298593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298593
  have eq371972 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq139525
    | (have j0 := eq139525 (σ x) X0 X1
       grind)
    | exact resolve eq139525 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139525
  have eq374348 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq371972 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371972
  have eq374926 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq147832 eq374348
    | (have j0 := eq374348 X0
       grind)
    | (have r₁ := eq374348 X0
       have r₂ := eq147832
       grind)
    | exact resolve eq374348 eq147832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147832
  have eq374927 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq374926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374926
  have eq374929 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq374927 X0
       grind)
    | (have r₁ := eq374927 X0
       have r₂ := eq147859
       grind)
    | exact resolve eq374927 eq147859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147859 eq374927
  have eq375886 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq374929
  have eq377770 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq375886 eq48612
    | exact resolve eq48612 eq375886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48612 eq375886
  have eq377805 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq377770
  have eq377818 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq377805
       have r₂ := eq147836
       grind)
    | exact resolve eq377805 eq147836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147836 eq377805
  have eq377840 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq377818 eq645
    | exact resolve eq645 eq377818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq377887 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq377840
    | exact resolve eq377840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377840
  have eq377895 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq377818 eq377887
    | exact resolve eq377887 eq377818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377818 eq377887
  have eq377932 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq377895
  have eq378413 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq377932 eq60
    | exact resolve eq60 eq377932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq377932
  have eq378492 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq378413
    | exact resolve eq378413 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq378413
  have eq379028 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq378492
       grind)
    | exact superpose eq378492 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq378492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378492
  have eq379038 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq379028
  have eq379709 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq299052 x
       have i₂ := eq379038
       grind)
    | exact superpose eq379038 eq299052
    | exact resolve eq299052 eq379038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299052
  have eq379923 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq379709
  have eq381101 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq45949 X0
       have i₂ := eq379923
       grind)
    | exact superpose eq379923 eq45949
    | (have j0 := eq45949 x
       grind)
    | exact resolve eq45949 eq379923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45949
  have eq381113 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq379038
       have i₂ := eq379923
       grind)
    | exact superpose eq379923 eq379038
    | exact resolve eq379038 eq379923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379038 eq379923
  have eq381349 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq381113
  have eq381360 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq381101 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381101
  have eq381381 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq381360 X0
       have j1 := eq221145 X0
       grind)
    | (have r₁ := eq381360 X0
       have r₂ := eq221145 X0
       grind)
    | (have r₁ := eq381360 x
       have r₂ := eq221145 X0
       grind)
    | exact resolve eq381360 eq221145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221145 eq381360
  have eq381390 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq381349 eq21
    | exact resolve eq21 eq381349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381349
  have eq381619 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq381390
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq381390
    | exact resolve eq381390 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381390
  have eq382528 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22633 X0
       have i₂ := eq381381 sF0
       grind)
    | exact superpose eq381381 eq22633
    | exact resolve eq22633 eq381381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381381
  have eq382630 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq382528 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq382528
    | (have j0 := eq382528 X0
       grind)
    | exact resolve eq382528 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382528
  have eq383241 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq382630
    | (have j0 := eq382630 (σ x)
       grind)
    | exact resolve eq382630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq382630
  have eq384114 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq383241 eq28
    | exact resolve eq28 eq383241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383241
  have eq384185 : x = (M.op x y) := by
    first
    | (have r₁ := eq384114
       have r₂ := eq381619
       grind)
    | exact resolve eq384114 eq381619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381619 eq384114
  have eq384188 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq384185 eq21
    | exact resolve eq21 eq384185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384260 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq384185 eq22633
    | exact resolve eq22633 eq384185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22633
  have eq384357 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq384260 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq384260
    | (have j0 := eq384260 X0
       grind)
    | exact resolve eq384260 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384260
  have eq384425 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq384188
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq384188
    | exact resolve eq384188 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384188
  have eq384438 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq384357
    | (have j0 := eq384357 X0
       grind)
    | exact resolve eq384357 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq384357
  have eq384566 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq384425 eq150295
    | exact resolve eq150295 eq384425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150295
  have eq384590 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq384566
       have r₂ := eq28
       grind)
    | exact resolve eq384566 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384566
  have eq394523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq384438 eq384590
    | exact resolve eq384590 eq384438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384590
  have eq394524 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq394523
       have r₂ := eq28
       grind)
    | exact resolve eq394523 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394523
  have eq394526 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq394524 eq28
    | exact resolve eq28 eq394524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq394577 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq394524 eq374348
    | (have j0 := eq374348 X0
       grind)
    | (have r₁ := eq374348 X0
       have r₂ := eq394524
       grind)
    | exact resolve eq374348 eq394524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374348
  have eq394582 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq394577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394577
  have eq394586 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq384425 eq394582
    | (have j0 := eq394582 X0
       grind)
    | exact resolve eq394582 eq384425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394582
  have eq395900 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq394586 X0
       grind)
    | (have r₁ := eq394586 X0
       have r₂ := eq394526
       grind)
    | exact resolve eq394586 eq394526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394586
  have eq396009 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq395900 eq25274
    | exact resolve eq25274 eq395900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25274 eq395900
  have eq396651 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq384425 eq396009
    | exact resolve eq396009 eq384425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396009
  have eq396818 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq384438 eq396651
    | exact resolve eq396651 eq384438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384438 eq396651
  have eq396888 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq396818
       have r₂ := eq394526
       grind)
    | exact resolve eq396818 eq394526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396818
  have eq396908 : (σ x) = (σ y) ∨ y = (k y y) := by
    first
    | exact superpose eq394524 eq396888
    | exact resolve eq396888 eq394524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394524 eq396888
  have eq396914 : (σ (M.op x y)) = (σ y) ∨ y = (k y y) := by
    first
    | exact superpose eq384425 eq396908
    | exact resolve eq396908 eq384425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396908
  have eq396916 : y = (k y y) := by
    first
    | (have r₁ := eq396914
       have r₂ := eq394526
       grind)
    | exact resolve eq396914 eq394526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396914
  have eq397041 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq396916
       grind)
    | exact superpose eq396916 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq396916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396916
  have eq397051 : y = (M.op y y) := by grind
  clear eq397041
  have eq397141 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq209 y
       have i₂ := eq397051
       grind)
    | exact superpose eq397051 eq209
    | exact resolve eq209 eq397051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq397524 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq384185 eq397141
    | exact resolve eq397141 eq384185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397141
  have eq397606 : y = (M.op x y) := by
    first
    | (have i₁ := eq397524
       have i₂ := eq397051
       grind)
    | exact superpose eq397051 eq397524
    | exact resolve eq397524 eq397051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397051 eq397524
  have eq397685 : y = (M.op x y) := by
    first
    | (have i₁ := eq397606
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq397606
    | exact resolve eq397606 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq397606
  have eq397764 : x = y := by
    first
    | exact superpose eq384185 eq397685
    | exact resolve eq397685 eq384185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384185 eq397685
  have eq397842 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq397764
       grind)
    | exact superpose eq397764 eq25
    | exact resolve eq25 eq397764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq397764
  have eq398196 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq397842
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq397842
    | exact resolve eq397842 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq397842
  have eq398267 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq384425 eq398196
    | exact resolve eq398196 eq384425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384425 eq398196
  have eq398327 : False := by grind
  exact eq398327

/-- `Equation4495`: `x ◇ (y ◇ y) = (z ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pyx_pxx_pyx_Equation4495 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X2) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X1)) X3) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq14 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 x X1 X3
       have i₂ := eq14 x X1 X0
       grind)
    | (have i₁ := eq14 (M.op (M.op X1 X1) X1) X1 x
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X3 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) X1) X2 X3
       have i₂ := eq14 X0 X1 (M.op X2 X2)
       grind)
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq14 X3 X1 X0
       grind)
    | (have i₁ := eq14 X0 X2 (M.op X2 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X2 (M.op X2 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 X1)) X1)
       have r₂ := eq14 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 (σ X0) (σ X1)
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq79
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq79 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq212 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op y y) X1)
       have i₂ := eq14 X0 X1 (M.op y y)
       grind)
    | (have i₁ := eq55 X0
       have i₂ := eq14 X0 y x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op y y) X0 X1
       have i₂ := eq55 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq535 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op x y) x) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X0 X1 X2 X3
       have i₂ := eq212 X3 X1
       grind)
    | exact superpose eq212 eq50
    | exact resolve eq50 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq582 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) x) X3) = (M.op X2 (M.op (M.op x y) x)) := by
    intro X2 X3
    first
    | (have i₁ := eq535 x x X2 X3
       have i₂ := eq371 x x
       grind)
    | (have i₁ := eq535 x y X2 X3
       have i₂ := eq371 x x
       grind)
    | exact superpose eq371 eq535
    | (have j0 := eq535 x y X2 X3
       grind)
    | exact resolve eq535 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq724 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op (M.op x y) x) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq53 x X1 X2 X3
       have i₂ := eq371 X1 x
       grind)
    | (have i₁ := eq53 x y X2 X3
       have i₂ := eq371 x X1
       grind)
    | exact superpose eq371 eq53
    | exact resolve eq53 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq725 : ∀ X3 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X3) := by
    intro X3
    first
    | (have i₁ := eq724 x x X3
       have i₂ := eq212 x (M.op x x)
       grind)
    | exact superpose eq212 eq724
    | exact resolve eq724 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq843 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X3 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq52
    | (have j1 := eq87 X0 X1
       grind)
    | exact resolve eq52 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq87
  have eq848 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1 x x
       have i₂ := eq212 x x
       grind)
    | exact superpose eq212 eq843
    | (have j0 := eq843 X0 X1 x x
       grind)
    | exact resolve eq843 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq857 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op x y) x) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq371 X1 X0
       grind)
    | (have i₁ := eq68 x y X2
       have i₂ := eq371 X0 X1
       grind)
    | exact superpose eq371 eq68
    | (have j0 := eq68 X0 X1 X2
       grind)
    | exact resolve eq68 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq858 : ∀ X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq857 x X1 X2
       have i₂ := eq371 X1 x
       grind)
    | (have i₁ := eq857 x y X2
       have i₂ := eq371 x X1
       grind)
    | exact superpose eq371 eq857
    | (have j0 := eq857 x X1 X2
       grind)
    | exact resolve eq857 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq867 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq725 eq858
    | (have r₁ := eq858 (M.op (M.op x y) x) x
       have r₂ := eq725 (M.op (M.op x y) x)
       grind)
    | exact resolve eq858 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq870 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq103 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1147
    | exact resolve eq1147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1151 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1148
       have r₂ := eq27
       grind)
    | exact resolve eq1148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1155 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1151 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1151
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1151
       grind)
    | exact resolve eq13 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1162 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1155
  have eq1175 : (τ (σ x)) = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1162 eq62
    | exact resolve eq62 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1162
  have eq1177 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1175
    | exact resolve eq1175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1175
  have eq1203 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73 x y
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq73
    | (have j0 := eq73 y x
       grind)
    | exact resolve eq73 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1204 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1203
  have eq1206 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1204
    | exact resolve eq1204 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1210 : x ≠ x ∨ y = (M.op x y) ∨ (M.op y y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1206
       grind)
    | exact superpose eq1206 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1206
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1206
       grind)
    | exact resolve eq12 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1206
       grind)
    | exact superpose eq1206 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq1206
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1206
       grind)
    | exact resolve eq13 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq371 x y
       have i₂ := eq1206
       grind)
    | exact superpose eq1206 eq371
    | exact resolve eq371 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1218 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1211
  have eq1219 : y = (M.op x y) ∨ (M.op y y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1210
  have eq1220 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1216
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1216
    | exact resolve eq1216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1225 : y = (M.op x y) ∨ (M.op y y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1219
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1219
    | exact resolve eq1219 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1219
  have eq1226 : (M.op y y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1225
  have eq1237 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1220 eq582
    | exact resolve eq582 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq1240 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1220 eq725
    | exact resolve eq725 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1243 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1220 eq870
    | exact resolve eq870 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq1220
  have eq1376 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1243 eq136
    | exact resolve eq136 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq1243
  have eq1377 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1376
    | exact resolve eq1376 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq1386 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1377 eq73
    | (have j0 := eq73 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq73 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1387 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq1386
  have eq1415 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1387 eq212
    | exact resolve eq212 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1618 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1237 X0 (M.op x y)
       have i₂ := eq1237 sF0 X1
       grind)
    | exact superpose eq1237 eq1237
    | exact resolve eq1237 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1697 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1618 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq2900 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1415 eq1387
    | exact resolve eq1387 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387 eq1415
  have eq2902 : (σ (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq2900
  have eq2964 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2902 eq1240
    | exact resolve eq1240 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq2966 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2902 eq1697
    | exact resolve eq1697 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq2977 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2966 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2966
  have eq2979 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2964
  have eq8130 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq848 x y
       have i₂ := eq1218
       grind)
    | exact superpose eq1218 eq848
    | (have j0 := eq848 x y
       grind)
    | exact resolve eq848 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq1218
  have eq8275 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8130
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8130
    | exact resolve eq8130 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8130
  have eq8327 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8275
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8275
    | exact resolve eq8275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8275
  have eq8360 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8327
    | exact resolve eq8327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8327
  have eq8369 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8360
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8360
    | exact resolve eq8360 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq8375 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8369
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8369
    | exact resolve eq8369 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8369
  have eq8376 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8375
    | exact resolve eq8375 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8375
  have eq86024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8376 eq2902
    | exact resolve eq2902 eq8376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902 eq8376
  have eq86085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86024
  have eq86110 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq86085
       have r₂ := eq27
       grind)
    | exact resolve eq86085 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86085
  have eq86114 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86110 eq71
    | (have r₁ := eq71
       have r₂ := eq86110
       grind)
    | exact resolve eq71 eq86110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq86110
  have eq86121 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq86114
  have eq86126 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86121 eq86
    | exact resolve eq86 eq86121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq86121
  have eq86141 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq86126
    | exact resolve eq86126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq86126
  have eq86157 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1226
       have i₂ := eq86141
       grind)
    | exact superpose eq86141 eq1226
    | exact resolve eq1226 eq86141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq86141
  have eq86170 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq86157
  have eq86199 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq86170
       grind)
    | exact superpose eq86170 eq55
    | exact resolve eq55 eq86170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq87336 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq86199 eq2977
    | exact resolve eq2977 eq86199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977 eq86199
  have eq87498 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq87336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87336
  have eq87637 : y = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq86170
       have i₂ := eq87498 y
       grind)
    | exact superpose eq87498 eq86170
    | exact resolve eq86170 eq87498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86170 eq87498
  have eq87738 : y = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq87637
  have eq87839 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87738 eq2979
    | exact resolve eq2979 eq87738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979 eq87738
  have eq88065 : y = (M.op x y) := by grind
  clear eq87839
  have eq88125 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq88065 eq20
    | exact resolve eq20 eq88065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq88128 : y ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq88065 eq70
    | (have r₁ := eq70
       have r₂ := eq88065
       grind)
    | exact resolve eq70 eq88065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq88276 : y = (k y x) := by grind
  clear eq88128
  have eq88399 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq88125
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq88125
    | exact resolve eq88125 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88125
  have eq89377 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq88399 eq26
    | exact resolve eq26 eq88399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq89462 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq88276
       grind)
    | exact superpose eq88276 eq79
    | exact resolve eq79 eq88276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq88276
  have eq89503 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq88399 eq89462
    | exact resolve eq89462 eq88399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89462
  have eq89523 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq89503
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89503
    | exact resolve eq89503 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89503
  have eq89541 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq88399 eq89523
    | exact resolve eq89523 eq88399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88399 eq89523
  have eq90978 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq89541 eq73
    | (have j0 := eq73 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq73 eq89541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq90982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq89377 eq90978
    | exact resolve eq90978 eq89377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90978
  have eq90991 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq90982
       have r₂ := eq27
       grind)
    | exact resolve eq90982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90982
  have eq91039 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq90991 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq90991
       grind)
    | exact resolve eq12 eq90991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91045 : (M.op (M.op x y) x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq90991 eq371
    | exact resolve eq371 eq90991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90991
  have eq91048 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq91039
  have eq91049 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq89377 eq91045
    | exact resolve eq91045 eq89377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91045
  have eq91054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq89377 eq91048
    | exact resolve eq91048 eq89377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89377 eq91048
  have eq91055 : (M.op (σ x) (σ y)) = (M.op y x) := by
    first
    | exact superpose eq88065 eq91049
    | exact resolve eq91049 eq88065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91049
  have eq91060 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq91054
       have r₂ := eq27
       grind)
    | exact resolve eq91054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91054
  have eq91065 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq89541 eq91060
    | exact resolve eq91060 eq89541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89541 eq91060
  have eq92393 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq91065 eq371
    | exact resolve eq371 eq91065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq92396 : (σ (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq91065 eq92393
    | exact resolve eq92393 eq91065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91065 eq92393
  have eq92407 : (σ (M.op x y)) = (M.op y x) := by
    first
    | exact superpose eq88065 eq92396
    | exact resolve eq92396 eq88065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88065 eq92396
  have eq92417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92407
       have i₂ := eq91055
       grind)
    | exact superpose eq91055 eq92407
    | exact resolve eq92407 eq91055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91055 eq92407
  have eq92423 : False := by grind
  exact eq92423
