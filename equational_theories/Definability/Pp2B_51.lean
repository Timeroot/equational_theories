import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq31
    | exact resolve eq31 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq288 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq281
    | exact resolve eq281 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq339 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq9
    | exact resolve eq9 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       have j1 := eq339 X0 X1
       grind)
    | (have r₁ := eq457 X0 X1
       have r₂ := eq339 X0 X1
       grind)
    | exact resolve eq457 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq457
  have eq508 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq493 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq493
    | (have j0 := eq493 (τ X0) X1
       grind)
    | exact resolve eq493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq493 X1 (σ X0)
       grind)
    | exact superpose eq493 eq15
    | (have j1 := eq493 X1 (σ X0)
       grind)
    | exact resolve eq15 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq538 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq519
    | (have j0 := eq519 X0 X1
       grind)
    | exact resolve eq519 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq542 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq508
    | (have j0 := eq508 X0 X1
       grind)
    | exact resolve eq508 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq548 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq542 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq542
    | (have j0 := eq542 X0 X1
       grind)
    | exact resolve eq542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq575 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq548 X1 (τ X0)
       grind)
    | exact superpose eq548 eq17
    | (have j1 := eq548 X1 (τ X0)
       grind)
    | exact resolve eq17 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq548
  have eq584 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq575
    | (have j0 := eq575 X0 X1
       grind)
    | exact resolve eq575 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq575
  have eq710 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq584 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 (σ X0) X1
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq759 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq762 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq759
    | (have j0 := eq759 X0 X1
       grind)
    | exact resolve eq759 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq763 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1004 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq538 x y
       grind)
    | exact superpose eq538 eq16
    | (have j1 := eq538 x y
       grind)
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1004
       have i₂ := eq763 x y
       grind)
    | exact superpose eq763 eq1004
    | (have j1 := eq763 x y
       grind)
    | (have r₁ := eq1004
       have r₂ := eq763 x y
       grind)
    | exact resolve eq1004 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq1004
  have eq1027 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1026
  have eq1030 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq9
    | exact resolve eq9 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1051 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1030 X0
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq1030
    | exact resolve eq1030 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1057 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1051 X0
       grind)
    | exact superpose eq1051 eq10
    | (have j1 := eq1051 X0
       grind)
    | exact resolve eq10 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1098 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1057 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1057
    | (have j0 := eq1057 X0
       grind)
    | exact resolve eq1057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1103 : ∀ X0 X1 : G, (M.op y X0) = (M.op X0 (M.op X0 (M.op x x))) ∨ (M.op y X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq1098 X1
       grind)
    | exact superpose eq1098 eq9
    | (have j1 := eq1098 X1
       grind)
    | exact resolve eq9 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1125 : ∀ X0 X1 : G, (M.op y X0) = (M.op x X0) ∨ (M.op y X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq1103
    | (have j0 := eq1103 X0 X0
       grind)
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1171 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1125 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1172 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1203 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq1172 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq1172 eq9
    | exact resolve eq9 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1232 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1203 X0
       have i₂ := eq1172 (M.op X0 X0)
       grind)
    | exact superpose eq1172 eq1203
    | exact resolve eq1203 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1258 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1232 X0
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq1232
    | exact resolve eq1232 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1279 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ (M.op y x)))) := by
    intro X0
    first
    | (have i₁ := eq340 y X0
       have i₂ := eq1258 y
       grind)
    | exact superpose eq1258 eq340
    | exact resolve eq340 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq1279 X0
       have i₂ := eq1172 x
       grind)
    | exact superpose eq1172 eq1279
    | exact resolve eq1279 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1279
  have eq1324 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1307 X0
       have i₂ := eq340 x X0
       grind)
    | exact superpose eq340 eq1307
    | exact resolve eq1307 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq1307
  have eq1526 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y)
       have i₂ := eq1324 (M.op (σ y) (M.op X0 X0))
       grind)
    | exact superpose eq1324 eq9
    | exact resolve eq9 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1557 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1526 X0
       have i₂ := eq1324 (M.op X0 X0)
       grind)
    | exact superpose eq1324 eq1526
    | exact resolve eq1526 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324 eq1526
  have eq1599 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1557 X0
       have i₂ := eq9 X0 (σ x)
       grind)
    | exact superpose eq9 eq1557
    | exact resolve eq1557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1759 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1599 (σ x)
       grind)
    | exact superpose eq1599 eq16
    | exact resolve eq16 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq1775 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1759
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq1759
    | exact resolve eq1759 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq1759
  have eq1801 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1775
       have i₂ := eq1258 x
       grind)
    | exact superpose eq1258 eq1775
    | exact resolve eq1775 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq1775
  have eq1802 : False := by grind
  exact eq1802

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxy_pyy_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28
    | exact resolve eq28 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28
  have eq33 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq19
       have i₂ := eq34
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34
  have eq38 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq36
       have i₂ := eq33
       grind)
    | exact superpose eq33 eq36
    | exact resolve eq36 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq36
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq43 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op (M.op X2 (M.op (M.op X0 X2) X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X0 X2) X1) X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X0 X2) X1)) X3)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 X0 X1 X2 X3
       have i₂ := eq74 X3
       grind)
    | exact superpose eq74 eq43
    | exact resolve eq43 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq83 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (k X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X0 X1 X2 X3
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq44
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (k X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X0 X1 X2 X3
       have i₂ := eq74 X3
       grind)
    | exact superpose eq74 eq83
    | exact resolve eq83 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq91 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | (have r₁ := eq77 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq77 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq92 : ∀ X1 X3 : G, (k X3 X3) = (M.op X1 (M.op (k X1 X1) X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq82 x X1 x X3
       have i₂ := eq76 X1 x x
       grind)
    | exact superpose eq76 eq82
    | exact resolve eq82 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq118 : (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq38 eq101
    | (have j0 := eq101 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq101 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq168 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (k (M.op (k (k X0 X0) (k X0 X0)) X1) (M.op (k (k X0 X0) (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (M.op (k (k X0 X0) (k X0 X0)) X1)
       have i₂ := eq92 (k X0 X0) X1
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op (M.op (k X0 X0) X1) (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X2 (M.op (k X0 X0) X1) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq76
    | exact resolve eq76 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq217 : ∀ X1 X3 : G, (M.op X3 (k X1 X1)) = (k (M.op (k X3 X3) X1) (M.op (k X3 X3) X1)) := by
    intro X1 X3
    first
    | (have i₁ := eq76 (M.op (k X3 X3) X1) X3 (M.op x x)
       have i₂ := eq86 x X3 x X1
       grind)
    | exact superpose eq86 eq76
    | exact resolve eq76 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq86
  have eq224 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op (k X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq217 X1 (k X0 X0)
       grind)
    | exact superpose eq217 eq168
    | exact resolve eq168 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq443 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq224 X0 X0
       have i₂ := eq74 (k X0 X0)
       grind)
    | exact superpose eq74 eq224
    | exact resolve eq224 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq643 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq118 eq15
    | exact resolve eq15 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 : G, (k X0 X0) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op X0 (τ (σ y))) = (k X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq118 eq91
    | (have j0 := eq91 X0 (τ (σ x))
       grind)
    | (have r₁ := eq91 (τ (σ y)) (τ (σ x))
       have r₂ := eq118
       grind)
    | (have r₁ := eq91 (τ (σ x)) (τ (σ y))
       have r₂ := eq118
       grind)
    | exact resolve eq91 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq669 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq643
       have i₂ := eq15 (τ sF2) (τ sF2)
       grind)
    | exact superpose eq15 eq643
    | exact resolve eq643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq672 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq669
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq669
    | exact resolve eq669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq675 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq672
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq672
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq985 : ∀ X0 : G, (k X0 X0) = (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (M.op (k X0 X0) X0)
       have i₂ := eq172 X0 X0 X0
       grind)
    | exact superpose eq172 eq74
    | exact resolve eq74 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq172
  have eq997 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq985 X0
       have i₂ := eq217 X0 X0
       grind)
    | exact superpose eq217 eq985
    | exact resolve eq985 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq985
  have eq1015 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq997 X0
       grind)
    | exact superpose eq997 eq443
    | exact resolve eq443 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq997
  have eq1221 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (M.op (k X0 X0) X1) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (k X0 X0) X1
       have i₂ := eq1015 X0
       grind)
    | exact superpose eq1015 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | (have r₁ := eq91 X0 (k X0 X0)
       have r₂ := eq1015 X0
       grind)
    | (have r₁ := eq91 (k X0 X0) X0
       have r₂ := eq1015 X0
       grind)
    | exact resolve eq91 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1883 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq675 eq15
    | exact resolve eq15 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq1885 : (σ (τ (σ x))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1883
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq1883
    | exact resolve eq1883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1901 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq1885
    | exact resolve eq1885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq5378 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have j0 := eq646 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq5381 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq38 eq5378
    | exact resolve eq5378 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5378
  have eq9615 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq1221 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq16887 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1901 eq15
    | exact resolve eq15 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq16895 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16887
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq16887
    | exact resolve eq16887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16887
  have eq16896 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16895
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq16895
    | exact resolve eq16895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16895
  have eq16897 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq16896
    | exact resolve eq16896 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16896
  have eq157684 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq5381 eq9615
    | exact resolve eq9615 eq5381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq157975 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq38 eq157684
    | exact resolve eq157684 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157684
  have eq157976 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq157975
  have eq158019 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq157976 eq15
    | exact resolve eq15 eq157976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157976
  have eq158028 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq158019
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq158019
    | exact resolve eq158019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158019
  have eq158029 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq158028
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq158028
    | exact resolve eq158028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158028
  have eq158030 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq158029
    | exact resolve eq158029 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158029
  have eq158031 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq158030 eq15
    | exact resolve eq15 eq158030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158030
  have eq158042 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq158031
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq158031
    | exact resolve eq158031 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158031
  have eq158043 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq158042
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq158042
    | exact resolve eq158042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158042
  have eq158044 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq158043
    | exact resolve eq158043 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158043
  have eq158045 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq158044 eq31
    | exact resolve eq31 eq158044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158044
  have eq158139 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq158045
       have i₂ := eq101 sF3 sF2
       grind)
    | exact superpose eq101 eq158045
    | (have j1 := eq101 (σ x) (σ y)
       grind)
    | (have r₁ := eq158045
       have r₂ := eq101 (σ y) (σ x)
       grind)
    | exact resolve eq158045 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158045
  have eq158140 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq158139
  have eq158551 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq158140 eq139
    | exact resolve eq139 eq158140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158140
  have eq158554 : (k (τ (σ y)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq158551
       have i₂ := eq139 sF2 sF2
       grind)
    | exact superpose eq139 eq158551
    | exact resolve eq158551 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158551
  have eq159600 : ∀ X0 : G, (k X0 X0) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op X0 (τ (σ y))) = (k X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq158554 eq91
    | (have j0 := eq91 X0 (τ (σ x))
       grind)
    | (have r₁ := eq91 (τ (σ y)) (τ (σ x))
       have r₂ := eq158554
       grind)
    | (have r₁ := eq91 (τ (σ x)) (τ (σ y))
       have r₂ := eq158554
       grind)
    | exact resolve eq91 eq158554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158554
  have eq579965 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq159600 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159600
  have eq579978 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq38 eq579965
    | exact resolve eq579965 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579965
  have eq579987 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq579978 eq15
    | exact resolve eq15 eq579978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579978
  have eq579997 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq579987
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq579987
    | exact resolve eq579987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579987
  have eq579998 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq579997
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq579997
    | exact resolve eq579997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579997
  have eq579999 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq579998
    | exact resolve eq579998 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579998
  have eq580000 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq579999
  have eq580401 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq580000 eq139
    | exact resolve eq139 eq580000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq580000
  have eq586391 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq580401 eq9615
    | exact resolve eq9615 eq580401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580401
  have eq587326 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq38 eq586391
    | exact resolve eq586391 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq586391
  have eq587452 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq587326 eq15
    | exact resolve eq15 eq587326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587326
  have eq587454 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq587452
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq587452
    | exact resolve eq587452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587452
  have eq587455 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq587454
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq587454
    | exact resolve eq587454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587454
  have eq587456 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq587455
    | exact resolve eq587455 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq587455
  have eq587457 : (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq587456
  have eq587459 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq587457 eq31
    | exact resolve eq31 eq587457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq587559 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq587457 eq16897
    | exact resolve eq16897 eq587457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16897 eq587457
  have eq594081 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq587459
       have i₂ := eq101 sF3 sF2
       grind)
    | exact superpose eq101 eq587459
    | (have j1 := eq101 (σ x) (σ y)
       grind)
    | exact resolve eq587459 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq594082 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq594081
       have r₂ := eq587559
       grind)
    | exact resolve eq594081 eq587559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587559 eq594081
  have eq594141 : ∀ X0 : G, (k X0 X0) ≠ (k (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq594082 eq91
    | (have j0 := eq91 X0 (σ x)
       grind)
    | (have r₁ := eq91 (σ x) (σ y)
       have r₂ := eq594082
       grind)
    | (have r₁ := eq91 (σ y) (σ x)
       have r₂ := eq594082
       grind)
    | exact resolve eq91 eq594082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq594082
  have eq607193 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq594141 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594141
  have eq607197 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq607193
       have r₂ := eq587459
       grind)
    | exact resolve eq607193 eq587459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607193
  have eq609431 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq607197 eq9615
    | exact resolve eq9615 eq607197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9615 eq607197
  have eq613874 : False := by grind
  exact eq613874

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
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
  have eq71 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq87 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq119 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq687
    | exact resolve eq687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq691 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq688
       have r₂ := eq27
       grind)
    | exact resolve eq688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq693 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq691
    | exact resolve eq691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq695 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq693
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq699 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq695 eq51
    | (have r₁ := eq51
       have r₂ := eq695
       grind)
    | exact resolve eq51 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq702 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq699
  have eq882 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq702 eq87
    | exact resolve eq87 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq890 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq882
    | exact resolve eq882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq882
  have eq894 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq890
       have r₂ := eq50
       grind)
    | exact resolve eq890 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq897 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq80
    | exact resolve eq80 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq899 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq898
  have eq901 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq899
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq899
    | exact resolve eq899 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq902 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq901
  have eq903 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq897
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq897
    | exact resolve eq897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq906 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq902
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq902
    | exact resolve eq902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq909 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq906 eq27
    | exact resolve eq27 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq906 eq51
    | exact resolve eq51 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq906 eq72
    | (have r₁ := eq72
       have r₂ := eq906
       grind)
    | exact resolve eq72 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq906
  have eq914 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq912
  have eq959 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq903 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq960 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq959
  have eq964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq960
    | exact resolve eq960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq965 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq964
  have eq970 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq965
    | exact resolve eq965 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1055 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq970 eq27
    | exact resolve eq27 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1202 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq914 eq87
    | exact resolve eq87 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq914
  have eq1213 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1202
    | exact resolve eq1202 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1202
  have eq1218 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1213
       have r₂ := eq71
       grind)
    | exact resolve eq1213 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1226 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1218
       grind)
    | exact superpose eq1218 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1227 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1226
  have eq1229 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1227
    | exact resolve eq1227 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1230 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1229
  have eq1235 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1230
    | exact resolve eq1230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1230
  have eq1342 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1235 eq106
    | exact resolve eq106 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1351 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1235 eq910
    | (have r₁ := eq910
       have r₂ := eq1235
       grind)
    | exact resolve eq910 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq1235
  have eq1357 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1351
  have eq1358 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1357
  have eq1364 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1342
  have eq1551 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1364 eq1358
    | exact resolve eq1358 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358 eq1364
  have eq1555 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1551
  have eq1559 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1555
       have r₂ := eq909
       grind)
    | exact resolve eq1555 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq1555
  have eq1561 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1559 eq20
    | exact resolve eq20 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1559 eq50
    | (have r₁ := eq50
       have r₂ := eq1559
       grind)
    | exact resolve eq50 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1575 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1563
  have eq1584 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1561
    | exact resolve eq1561 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1586 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1584 eq26
    | exact resolve eq26 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1584 eq1055
    | (have r₁ := eq1055
       have r₂ := eq1584
       grind)
    | exact resolve eq1055 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1610 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1604
  have eq1611 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1610
  have eq1631 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1611 eq27
    | exact resolve eq27 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1642 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq1575
       grind)
    | exact superpose eq1575 eq80
    | exact resolve eq80 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq1648 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1642
    | exact resolve eq1642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1654 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1586 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1586
       grind)
    | exact resolve eq12 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1654
       have r₂ := eq1611
       grind)
    | exact resolve eq1654 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611 eq1654
  have eq1670 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1669
       have r₂ := eq27
       grind)
    | exact resolve eq1669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1731 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1584 eq1648
    | exact resolve eq1648 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584 eq1648
  have eq1753 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1731
  have eq1768 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1753 eq1670
    | exact resolve eq1670 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq1753
  have eq1772 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1768
  have eq1776 : x = (M.op x y) := by
    first
    | (have r₁ := eq1772
       have r₂ := eq1631
       grind)
    | exact resolve eq1772 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq1772
  have eq1795 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1776 eq20
    | exact resolve eq20 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1797 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq1776 eq50
    | exact resolve eq50 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1799 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1776 eq71
    | (have r₁ := eq71
       have r₂ := eq1776
       grind)
    | exact resolve eq71 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1811 : y = (k y x) ∨ x = y := by grind
  clear eq1799
  have eq1821 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1795
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1795
    | exact resolve eq1795 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1822 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1821 eq26
    | exact resolve eq26 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2038 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq1811
       grind)
    | exact superpose eq1811 eq80
    | exact resolve eq80 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1811
  have eq2047 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1821 eq2038
    | exact resolve eq2038 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2051 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq2047
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2047
    | exact resolve eq2047 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2061 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2051 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq2061
  have eq2065 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1822 eq2062
    | exact resolve eq2062 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1822 eq2065
    | exact resolve eq2065 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2071 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2068
       have r₂ := eq27
       grind)
    | exact resolve eq2068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2076 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq2071 eq27
    | exact resolve eq27 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2071 eq51
    | (have r₁ := eq51
       have r₂ := eq2071
       grind)
    | exact resolve eq51 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2071
  have eq2085 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq2077
  have eq2088 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1821 eq2085
    | exact resolve eq2085 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq2304 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2088 eq2051
    | exact resolve eq2051 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq2305 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2088 eq119
    | exact resolve eq119 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq2088
  have eq2308 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2304
  have eq2313 : (τ (σ (M.op x y))) = (k y x) ∨ x = y := by
    first
    | exact superpose eq1776 eq2305
    | exact resolve eq2305 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2314 : x = y := by
    first
    | (have r₁ := eq2308
       have r₂ := eq2076
       grind)
    | exact resolve eq2308 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076 eq2308
  have eq2318 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq2313
    | exact resolve eq2313 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2313
  have eq2321 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1776 eq2318
    | exact resolve eq2318 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq2318
  have eq2323 : x = (k y x) := by
    first
    | (have r₁ := eq2321
       have r₂ := eq1797
       grind)
    | exact resolve eq2321 eq1797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797 eq2321
  have eq2325 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq24
    | exact resolve eq24 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2358 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2325
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2325
    | exact resolve eq2325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2368 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1821 eq2358
    | exact resolve eq2358 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq2396 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2368 eq1822
    | exact resolve eq1822 eq2368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822 eq2368
  have eq2423 : x = (k x x) := by
    first
    | (have i₁ := eq2323
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq2323
    | exact resolve eq2323 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314 eq2323
  have eq2425 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2423
       grind)
    | exact superpose eq2423 eq43
    | exact resolve eq43 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2423
  have eq2429 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1821 eq2425
    | exact resolve eq2425 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq2430 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2429
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2429
    | exact resolve eq2429 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2429
  have eq2431 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1821 eq2430
    | exact resolve eq2430 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821 eq2430
  have eq2765 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2431 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq2766 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2765
  have eq2801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2396 eq2766
    | exact resolve eq2766 eq2396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396 eq2766
  have eq2802 : False := by grind
  exact eq2802

/-- `Equation3495`: `x ◇ x = y ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3495 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3495 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3495.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq687
    | exact resolve eq687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq691 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq688
       have r₂ := eq27
       grind)
    | exact resolve eq688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq693 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq691
    | exact resolve eq691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq695 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq693
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq698 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq695 eq72
    | (have r₁ := eq72
       have r₂ := eq695
       grind)
    | exact resolve eq72 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq695
  have eq703 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq698
  have eq881 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq703
       have r₂ := eq702
       grind)
    | exact resolve eq703 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq703
  have eq885 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq881 eq87
    | exact resolve eq87 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq893 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq885
    | exact resolve eq885 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq885
  have eq897 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq893
       have r₂ := eq71
       grind)
    | exact resolve eq893 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq908 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq80
    | exact resolve eq80 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq910 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq909
  have eq912 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq910
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq910
    | exact resolve eq910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq913 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq912
  have eq914 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq908
    | exact resolve eq908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq917 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq913
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq913
    | exact resolve eq913 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq921 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq917 eq51
    | (have r₁ := eq51
       have r₂ := eq917
       grind)
    | exact resolve eq51 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq924 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq921
  have eq1013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq914 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1014 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1013
  have eq1018 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1014
    | exact resolve eq1014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1019 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1018
  have eq1024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1019
    | exact resolve eq1019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1026 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1024 eq27
    | exact resolve eq27 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1170 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq924 eq87
    | exact resolve eq87 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1181 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1170
    | exact resolve eq1170 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1184 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1181
       have r₂ := eq50
       grind)
    | exact resolve eq1181 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1190 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1191 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1190
  have eq1193 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1191
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1191
    | exact resolve eq1191 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1194 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1193
  have eq1198 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1194
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1194
    | exact resolve eq1194 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1194
  have eq1200 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1198 eq20
    | exact resolve eq20 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1198 eq71
    | (have r₁ := eq71
       have r₂ := eq1198
       grind)
    | exact resolve eq71 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1213 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1198
  have eq1214 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1204
  have eq1224 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1200
    | exact resolve eq1200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1224 eq1026
    | (have r₁ := eq1026
       have r₂ := eq1224
       grind)
    | exact resolve eq1026 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1224
  have eq1296 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1293
  have eq1297 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1296
  have eq1417 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1297 eq51
    | (have r₁ := eq51
       have r₂ := eq1297
       grind)
    | exact resolve eq51 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1297
  have eq1420 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1417
  have eq1463 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1420 eq87
    | exact resolve eq87 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1420
  have eq1478 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1463
    | exact resolve eq1463 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1463
  have eq1481 : y = (k y x) := by
    first
    | (have r₁ := eq1478
       have r₂ := eq50
       grind)
    | exact resolve eq1478 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1478
  have eq1543 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq80
    | exact resolve eq80 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1548 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1543
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1543
    | exact resolve eq1543 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1543
  have eq1561 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1548 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1562 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1561
  have eq1564 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1562
    | exact resolve eq1562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1567 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1564
    | exact resolve eq1564 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1564
  have eq1572 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1567 eq72
    | (have r₁ := eq72
       have r₂ := eq1567
       grind)
    | exact resolve eq72 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1576 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1567
  have eq1577 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1572
  have eq1578 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1548 eq1577
    | exact resolve eq1577 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq1577
  have eq1579 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1578
  have eq1597 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1579
       have r₂ := eq1576
       grind)
    | exact resolve eq1579 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq1579
  have eq1601 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1597 eq27
    | exact resolve eq27 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1597
  have eq2663 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1214
       have r₂ := eq1213
       grind)
    | exact resolve eq1214 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq2664 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2663
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq2663
    | exact resolve eq2663 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq2663
  have eq2665 : x = (M.op x y) := by
    first
    | (have r₁ := eq2664
       have r₂ := eq1213
       grind)
    | exact resolve eq2664 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq2664
  have eq2667 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2665 eq20
    | exact resolve eq20 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2665
  have eq2692 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2667
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2667
    | exact resolve eq2667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2667
  have eq2694 : False := by grind
  exact eq2694

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_x_x_pxy_pyx_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq9 X0 (M.op x x) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq58 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x x) X0) x
       grind)
    | (have i₁ := eq58 X0 x X2
       have i₂ := eq9 (M.op (M.op x x) X0) x X2
       grind)
    | exact superpose eq9 eq58
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq149 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq108
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq108
  have eq164 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq160 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq160
    | exact resolve eq160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq216 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq239 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq72
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq262 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq254
    | exact resolve eq254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq264 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq149
  have eq324 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164
    | (have j0 := eq164 x
       grind)
    | exact resolve eq164 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq164 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq164
    | (have j0 := eq164 y
       grind)
    | exact resolve eq164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq357 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq264 (M.op X0 X0)
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq264
    | exact resolve eq264 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq2258 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq239 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq239
    | (have j0 := eq239 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq239 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq239
  have eq2370 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2258 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2892 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ (M.op X0 X0)) x
       have i₂ := eq2370 X0
       grind)
    | exact superpose eq2370 eq62
    | exact resolve eq62 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq3794 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq14
    | (have j0 := eq14 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       grind)
    | exact resolve eq14 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3795 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794
  have eq5657 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ (M.op X0 X0)) x
       have i₂ := eq3795 X0
       grind)
    | exact superpose eq3795 eq62
    | exact resolve eq62 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795
  have eq17969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq262
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq262
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq262 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17969
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17969
    | exact resolve eq17969 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17969
  have eq18005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq18002
    | exact resolve eq18002 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18002
  have eq18006 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18005
       have r₂ := eq28
       grind)
    | exact resolve eq18005 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18005
  have eq19072 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18006 eq357
    | exact resolve eq357 eq18006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq18006
  have eq19135 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq40 eq19072
    | exact resolve eq19072 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19072
  have eq19385 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq19135
       grind)
    | exact superpose eq19135 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq19135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19135
  have eq19386 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq19385
  have eq19391 : y = (k y (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19386 eq325
    | exact resolve eq325 eq19386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq19404 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19386 eq62
    | exact resolve eq62 eq19386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19386
  have eq19484 : y = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq39 eq19391
    | exact resolve eq19391 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19391
  have eq19622 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op X1 (σ x)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq2892 y X1
       have i₂ := eq19404 X0
       grind)
    | exact superpose eq19404 eq2892
    | (have j1 := eq19404 X1
       grind)
    | exact resolve eq2892 eq19404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19404
  have eq19668 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op X1 (σ x)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq19622 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19622
    | (have j0 := eq19622 X0 X1
       grind)
    | exact resolve eq19622 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19622
  have eq19845 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19484
       grind)
    | exact superpose eq19484 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq19484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19484
  have eq19846 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq19845
  have eq19848 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19846
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19846
    | exact resolve eq19846 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19846
  have eq19865 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq62 y x
       have i₂ := eq19848
       grind)
    | exact superpose eq19848 eq62
    | exact resolve eq62 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19919 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq19848
  have eq20049 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ x = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq62 y x
       have i₂ := eq19865 X0
       grind)
    | exact superpose eq19865 eq62
    | (have j1 := eq19865 X1
       grind)
    | exact resolve eq62 eq19865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq19865
  have eq22259 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq20049 X0 x
       grind)
    | exact superpose eq20049 eq19
    | (have j1 := eq20049 X0 x
       grind)
    | exact resolve eq19 eq20049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20049
  have eq22374 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22259
  have eq22416 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq217 x x
       have i₂ := eq22374 x
       grind)
    | exact superpose eq22374 eq217
    | exact resolve eq217 eq22374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22436 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2892 x x
       have i₂ := eq22374 x
       grind)
    | exact superpose eq22374 eq2892
    | exact resolve eq2892 eq22374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22374
  have eq22527 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22436 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22436
    | (have j0 := eq22436 X0
       grind)
    | exact resolve eq22436 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22436
  have eq22560 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22527 eq217
    | exact resolve eq217 eq22527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22527
  have eq60478 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22560 eq43
    | (have j1 := eq22560 (σ y)
       grind)
    | exact resolve eq43 eq22560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22560
  have eq60613 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq60478
    | exact resolve eq60478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60478
  have eq61047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60613
       have i₂ := eq22416 y
       grind)
    | exact superpose eq22416 eq60613
    | (have j1 := eq22416 y
       grind)
    | exact resolve eq60613 eq22416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22416 eq60613
  have eq61079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq61047
  have eq61090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq61079
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61079
    | exact resolve eq61079 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61079
  have eq61095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq61090
    | exact resolve eq61090 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61090
  have eq61098 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq61095
       have r₂ := eq28
       grind)
    | exact resolve eq61095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61095
  have eq61103 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61098 eq40
    | exact resolve eq40 eq61098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61098
  have eq61165 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq61103
    | exact resolve eq61103 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61103
  have eq61166 : y = (M.op x y) ∨ x = y := by grind
  clear eq61165
  have eq61170 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq61166 eq21
    | exact resolve eq21 eq61166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61166
  have eq61190 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61170
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq61170
    | exact resolve eq61170 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61170
  have eq517340 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19668 eq27
    | (have j1 := eq19668 (σ x) X0
       grind)
    | exact resolve eq27 eq19668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19668
  have eq517686 : ∀ X0 X1 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X1 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2892 y X1
       have i₂ := eq517340 X0
       grind)
    | exact superpose eq517340 eq2892
    | (have j1 := eq517340 X0
       grind)
    | exact resolve eq2892 eq517340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq517340
  have eq517694 : ∀ X0 X1 : G, (σ x) = (M.op X1 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq517686 X1 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq517686
    | (have j0 := eq517686 X1 X1
       grind)
    | exact resolve eq517686 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517686
  have eq518920 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq517694 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517694
  have eq518921 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq518920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518920
  have eq519411 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq518921 eq217
    | exact resolve eq217 eq518921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519444 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq518921 eq5657
    | exact resolve eq5657 eq518921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657
  have eq519604 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq518921 eq324
    | exact resolve eq324 eq518921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq518921
  have eq519693 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39 eq519604
    | exact resolve eq519604 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519604
  have eq519723 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq519444
    | exact resolve eq519444 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519444
  have eq521071 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq217 x x
       have i₂ := eq519723 x
       grind)
    | exact superpose eq519723 eq217
    | exact resolve eq217 eq519723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq519723
  have eq568041 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq519411 eq43
    | (have j1 := eq519411 (σ y)
       grind)
    | exact resolve eq43 eq519411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq519411
  have eq568054 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq568041
    | exact resolve eq568041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568041
  have eq571859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq568054
       have i₂ := eq521071 y
       grind)
    | exact superpose eq521071 eq568054
    | (have j1 := eq521071 y
       grind)
    | exact resolve eq568054 eq521071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521071 eq568054
  have eq571871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq571859
  have eq571875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq571871
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq571871
    | exact resolve eq571871 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571871
  have eq571880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq571875
    | exact resolve eq571875 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571875
  have eq571881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq571880
       have r₂ := eq28
       grind)
    | exact resolve eq571880 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571880
  have eq572134 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq571881 eq28
    | exact resolve eq28 eq571881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571881
  have eq572230 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq572134
       have r₂ := eq61190
       grind)
    | exact resolve eq572134 eq61190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61190 eq572134
  have eq572236 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq572230 eq40
    | exact resolve eq40 eq572230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq572230
  have eq572629 : x = y ∨ x = y := by
    first
    | exact superpose eq39 eq572236
    | exact resolve eq572236 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq572236
  have eq572630 : x = y := by grind
  clear eq572629
  have eq572634 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq572630
       grind)
    | exact superpose eq572630 eq19
    | exact resolve eq19 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq572635 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq572630
       grind)
    | exact superpose eq572630 eq25
    | exact resolve eq25 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq572652 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq262
       have i₂ := eq572630
       grind)
    | exact superpose eq572630 eq262
    | exact resolve eq262 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq573946 : x = (M.op x x) ∨ x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19919
       have i₂ := eq572630
       grind)
    | exact superpose eq572630 eq19919
    | (have r₁ := eq19919
       have r₂ := eq572630
       grind)
    | exact resolve eq19919 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19919
  have eq611452 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq573946
       have r₂ := eq572630
       grind)
    | exact resolve eq573946 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573946
  have eq611538 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq572635
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq572635
    | exact resolve eq572635 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572635
  have eq611831 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq611452
       have i₂ := eq572634
       grind)
    | exact superpose eq572634 eq611452
    | exact resolve eq611452 eq572634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572634 eq611452
  have eq611889 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq611538 eq27
    | exact resolve eq27 eq611538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq612028 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq611538 eq519693
    | exact resolve eq519693 eq611538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519693
  have eq613190 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq611538 eq572652
    | exact resolve eq572652 eq611538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572652
  have eq615343 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq611831
       have i₂ := eq572630
       grind)
    | exact superpose eq572630 eq611831
    | exact resolve eq611831 eq572630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572630 eq611831
  have eq615344 : x = (M.op x y) := by grind
  clear eq615343
  have eq615679 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | exact superpose eq611538 eq613190
    | exact resolve eq613190 eq611538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611538 eq613190
  have eq615680 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by grind
  clear eq615679
  have eq616501 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq615344 eq21
    | exact resolve eq21 eq615344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq615344
  have eq619707 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | exact superpose eq611889 eq615680
    | exact resolve eq615680 eq611889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611889 eq615680
  have eq620196 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq616501
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq616501
    | exact resolve eq616501 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616501
  have eq620434 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq620196 eq23
    | exact resolve eq23 eq620196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq621716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq620196 eq612028
    | exact resolve eq612028 eq620196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612028
  have eq623040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | exact superpose eq620196 eq619707
    | exact resolve eq619707 eq620196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619707 eq620196
  have eq623522 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | (have r₁ := eq623040
       have r₂ := eq28
       grind)
    | exact resolve eq623040 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623040
  have eq624478 : x = (k x x) := by
    first
    | (have r₁ := eq621716
       have r₂ := eq28
       grind)
    | exact resolve eq621716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621716
  have eq626253 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq623522
       have i₂ := eq624478
       grind)
    | exact superpose eq624478 eq623522
    | exact resolve eq623522 eq624478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623522 eq624478
  have eq627460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq626253
       have i₂ := eq620434
       grind)
    | exact superpose eq620434 eq626253
    | exact resolve eq626253 eq620434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620434 eq626253
  have eq628247 : False := by grind
  exact eq628247

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pyy_pxx_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq24
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 (M.op (M.op x x) x) x x
       have i₂ := eq16 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ X3 ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 (M.op (M.op X2 X3) X3) X1
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op X1 (M.op (M.op X2 X3) X3)) (M.op X1 (M.op (M.op X2 X3) X3))
       have r₂ := eq16 (M.op X1 (M.op (M.op X2 X3) X3)) X1 X2 X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X3) X3) (M.op X0 X0)
       have r₂ := eq16 X0 (M.op X0 X0) X2 X3
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have r₁ := eq13 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3 X3
       have i₂ := eq181 X3 X0
       grind)
    | (have i₁ := eq16 X1 X2 X3 X3
       have i₂ := eq181 X0 X3
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ≠ X1 ∨ (k X1 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq13
    | (have r₁ := eq13 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq177 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 X0)
       have r₂ := eq177 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq480 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq507 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq423
    | exact resolve eq423 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq704 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ X3 ∨ (k X3 X3) = (M.op X0 (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq201 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 (M.op (M.op X0 X0) X3) X2
       have i₂ := eq201 X0 X1 X2 X3
       grind)
    | exact superpose eq201 eq13
    | (have r₁ := eq13 (M.op X2 (M.op (M.op X0 X0) X3)) (M.op X2 (M.op (M.op X0 X0) X3))
       have r₂ := eq201 X0 (M.op X2 (M.op (M.op X0 X0) X3)) X2 X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) X3) (M.op X1 X1)
       have r₂ := eq201 X0 X1 (M.op X1 X1) X3
       grind)
    | exact resolve eq13 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1658 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1660 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) ≠ (M.op X0 (M.op (M.op X1 X2) X2)) ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = X3 ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 X1 (M.op (M.op X2 X3) X3)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq12
    | (have r₁ := eq12 X1 (M.op (M.op X2 X3) X3)
       have r₂ := eq16 X1 X1 X2 X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3)
       have r₂ := eq16 (M.op (M.op X2 X3) X3) (M.op (M.op X2 X3) X3) X2 X3
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X1 ∨ (k X1 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq12 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq12
    | (have r₁ := eq12 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq177 X1 X1
       grind)
    | (have r₁ := eq12 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq177 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq12 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1665 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq181 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq181 X0 X0
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1666 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = X3 ∨ (k X3 X3) = (M.op X0 (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq201 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 X2 (M.op (M.op X0 X0) X3)
       have i₂ := eq201 X0 X1 X2 X3
       grind)
    | exact superpose eq201 eq12
    | (have r₁ := eq12 X2 (M.op (M.op X0 X0) X3)
       have r₂ := eq201 X0 X2 X2 X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X3) (M.op (M.op X0 X0) X3)
       have r₂ := eq201 X0 (M.op (M.op X0 X0) X3) (M.op (M.op X0 X0) X3) X3
       grind)
    | exact resolve eq12 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1691 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1696 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X3 ∨ (k X3 X3) = (M.op X0 (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1666 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1697 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq1700 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X1 ∨ (k X1 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq1662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1702 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = X3 ∨ (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1660 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1703 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1691 X0
       have j1 := eq200 X0 X0
       grind)
    | (have r₁ := eq1691 x
       have r₂ := eq200 x x
       grind)
    | (have r₁ := eq1691 (M.op X0 X0)
       have r₂ := eq200 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1691 X0
       have r₂ := eq200 X0 (k X0 X0)
       grind)
    | exact resolve eq1691 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1727 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op X0 (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1696 X0 X1 X2 (k X3 X3)
       have j1 := eq704 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1696 X0 X1 X2 X3
       have r₂ := eq704 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1696 X0 X1 X2 (M.op X0 (M.op (M.op X1 X1) X2))
       have r₂ := eq704 X0 X1 X2 (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | (have r₁ := eq1696 X0 X1 X2 X3
       have r₂ := eq704 X0 X1 X2 (k X3 X3)
       grind)
    | exact resolve eq1696 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq1696
  have eq1728 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1697 X0 (k X1 X1)
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq1697 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq1697 X0 (M.op X0 X0)
       have r₂ := eq200 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1697 X0 X1
       have r₂ := eq200 X0 (k X1 X1)
       grind)
    | exact resolve eq1697 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1731 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq1700 X0 (k X1 X1)
       have j1 := eq244 X0 X1
       grind)
    | (have r₁ := eq1700 X0 X1
       have r₂ := eq244 X0 X1
       grind)
    | (have r₁ := eq1700 X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq244 X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | (have r₁ := eq1700 X0 X1
       have r₂ := eq244 X0 (k X1 X1)
       grind)
    | exact resolve eq1700 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq1700
  have eq1733 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1702 X0 X1 X2 (k X3 X3)
       have j1 := eq185 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1702 X0 X1 X2 X3
       have r₂ := eq185 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1702 X0 X1 X2 (M.op X0 (M.op (M.op X1 X2) X2))
       have r₂ := eq185 X0 X1 X2 (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | (have r₁ := eq1702 X0 X1 X2 X3
       have r₂ := eq185 X0 X1 X2 (k X3 X3)
       grind)
    | exact resolve eq1702 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1702
  have eq1734 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq200 eq1659
    | (have j1 := eq200 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq1659
       have r₂ := eq200 (σ x) (k (σ x) (σ y))
       grind)
    | exact resolve eq1659 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1735 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq200 eq1658
    | (have j1 := eq200 x (M.op x y)
       grind)
    | (have r₁ := eq1658
       have r₂ := eq200 x (k x y)
       grind)
    | exact resolve eq1658 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1658
  have eq1757 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op X0 (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1727 X0 X1 X2 X3
       have i₂ := eq1703 X1
       grind)
    | exact superpose eq1703 eq1727
    | exact resolve eq1727 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1759 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1734
       have i₂ := eq1703 sF2
       grind)
    | exact superpose eq1703 eq1734
    | exact resolve eq1734 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1760 : (M.op x y) ≠ (k x x) ∨ y = (M.op y x) ∨ (k x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq1703 x
       grind)
    | exact superpose eq1703 eq1735
    | exact resolve eq1735 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1925 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1703 X0
       have i₂ := eq1728 X0 X1
       grind)
    | exact superpose eq1728 eq1703
    | exact resolve eq1703 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1955 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1728 X0 (σ X1)
       grind)
    | exact superpose eq1728 eq10
    | exact resolve eq10 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1956 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X1 (σ X1)
       have i₂ := eq1728 X0 (σ X1)
       grind)
    | exact superpose eq1728 eq480
    | exact resolve eq480 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq1958 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1728 X0 (τ X1)
       grind)
    | exact superpose eq1728 eq34
    | exact resolve eq34 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1728
  have eq1960 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1958 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq1958
    | exact resolve eq1958 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1961 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1956 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1956
    | exact resolve eq1956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq1981 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq1703 X0
       grind)
    | exact superpose eq1703 eq1960
    | exact resolve eq1960 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1982 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X0 X1
       have i₂ := eq1703 X0
       grind)
    | exact superpose eq1703 eq1961
    | exact resolve eq1961 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq2083 : ∀ X0 X2 : G, (σ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1955 x X2
       have i₂ := eq1955 x X0
       grind)
    | exact superpose eq1955 eq1955
    | exact resolve eq1955 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2267 : ∀ X0 X1 : G, (σ (k X0 X0)) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X1 X1
       have i₂ := eq1981 X0 (τ X1)
       grind)
    | exact superpose eq1981 eq507
    | exact resolve eq507 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2328 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1982 x X1
       have i₂ := eq1982 X0 x
       grind)
    | exact superpose eq1982 eq1982
    | exact resolve eq1982 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2355 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X1 X1
       have i₂ := eq1982 X0 (τ X1)
       grind)
    | exact superpose eq1982 eq507
    | exact resolve eq507 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2597 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1981 x X1
       have i₂ := eq1731 X0 x
       grind)
    | exact superpose eq1731 eq1981
    | exact resolve eq1981 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq3607 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1982 x X1
       have i₂ := eq2328 X0 x
       grind)
    | exact superpose eq2328 eq1982
    | exact resolve eq1982 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq3613 : ∀ X0 X1 : G, (σ (k X1 X1)) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2267 X1 x
       have i₂ := eq2328 X0 x
       grind)
    | exact superpose eq2328 eq2267
    | exact resolve eq2267 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq3619 : ∀ X0 X1 : G, (τ (k X1 X1)) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X1 X1
       have i₂ := eq2328 X0 (τ X1)
       grind)
    | exact superpose eq2328 eq507
    | exact resolve eq507 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq2328
  have eq4817 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (σ (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2597 (M.op sF4 sF3) X1
       have i₂ := eq201 X0 (M.op sF4 sF3) X2 X3
       grind)
    | exact superpose eq201 eq2597
    | exact resolve eq2597 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq2597
  have eq4902 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (σ (M.op X0 (M.op (k X1 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4817 X0 X1 X2 X3
       have i₂ := eq1703 X1
       grind)
    | exact superpose eq1703 eq4817
    | exact resolve eq4817 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq9758 : ∀ X0 X2 : G, (τ (k X2 X2)) = (τ (τ (τ (τ (k X0 X0))))) := by
    intro X0 X2
    first
    | (have i₁ := eq2355 x X2
       have i₂ := eq3607 X0 x
       grind)
    | exact superpose eq3607 eq2355
    | exact resolve eq2355 eq3607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355 eq3607
  have eq11575 : ∀ X0 X1 X2 X4 : G, (σ (k X4 X4)) = (σ (M.op X0 (M.op (k X1 X1) X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2083 x X4
       have i₂ := eq1757 X0 X1 X2 x
       grind)
    | exact superpose eq1757 eq2083
    | exact resolve eq2083 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757 eq2083
  have eq14827 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1563
       grind)
    | exact superpose eq1563 eq40
    | exact resolve eq40 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq14828 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14827
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14827
    | exact resolve eq14827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827
  have eq14830 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq14828
    | exact resolve eq14828 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14828
  have eq14832 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14830
       have i₂ := eq1703 x
       grind)
    | exact superpose eq1703 eq14830
    | exact resolve eq14830 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14830
  have eq523982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14832 eq1564
    | exact resolve eq1564 eq14832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523993 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq523982
       have r₂ := eq27
       grind)
    | exact resolve eq523982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523982
  have eq524001 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq523993
       have i₂ := eq1703 sF2
       grind)
    | exact superpose eq1703 eq523993
    | exact resolve eq523993 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523993
  have eq524113 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq524001 eq1759
    | (have r₁ := eq1759
       have r₂ := eq524001
       grind)
    | exact resolve eq1759 eq524001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq524130 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq524001 eq1925
    | exact resolve eq1925 eq524001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524001
  have eq524554 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by grind
  clear eq524113
  have eq524555 : (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by grind
  clear eq524554
  have eq524782 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq524130 eq524555
    | exact resolve eq524555 eq524130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524130 eq524555
  have eq524860 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14832 eq524782
    | exact resolve eq524782 eq14832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524782
  have eq524894 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq524860
       have r₂ := eq27
       grind)
    | exact resolve eq524860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524860
  have eq524922 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq524894 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq524894
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq524894
       grind)
    | exact resolve eq13 eq524894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524894
  have eq524955 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by grind
  clear eq524922
  have eq524986 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq524955
       have i₂ := eq1703 sF3
       grind)
    | exact superpose eq1703 eq524955
    | exact resolve eq524955 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524955
  have eq525000 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14832 eq524986
    | exact resolve eq524986 eq14832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14832 eq524986
  have eq525028 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq525000 eq1925
    | exact resolve eq1925 eq525000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525158 : ∀ X0 : G, (σ (k X0 X0)) = (τ (τ (τ (σ (M.op x y))))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq525000 eq3613
    | exact resolve eq3613 eq525000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq525359 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ (τ (τ (σ (M.op x y)))))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq525000 eq9758
    | exact resolve eq9758 eq525000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9758 eq525000
  have eq525502 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ (τ (M.op x y)))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq525359
    | exact resolve eq525359 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525359
  have eq525600 : ∀ X0 : G, (σ (k X0 X0)) = (τ (τ (M.op x y))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28 eq525158
    | exact resolve eq525158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525158
  have eq525725 : (τ (σ (M.op x y))) = (τ (τ (τ (M.op x y)))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq525028 eq525502
    | exact resolve eq525502 eq525028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525502
  have eq525784 : (σ (σ (M.op x y))) = (τ (τ (M.op x y))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq525028 eq525600
    | exact resolve eq525600 eq525028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525600
  have eq525858 : (M.op x y) = (τ (τ (τ (M.op x y)))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq525725
    | exact resolve eq525725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525725
  have eq525927 : (M.op x y) = (τ (σ (σ (M.op x y)))) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq525784 eq525858
    | exact resolve eq525858 eq525784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525784 eq525858
  have eq525964 : (M.op x y) = (k x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq525927
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq525927
    | exact resolve eq525927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525927
  have eq526014 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1925 x X0
       have i₂ := eq525964
       grind)
    | exact superpose eq525964 eq1925
    | exact resolve eq1925 eq525964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526017 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1981 x X0
       have i₂ := eq525964
       grind)
    | exact superpose eq525964 eq1981
    | exact resolve eq1981 eq525964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq526681 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq526017
    | (have j0 := eq526017 X0
       grind)
    | exact resolve eq526017 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526017
  have eq526844 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq526014 eq526681
    | exact resolve eq526681 eq526014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526014 eq526681
  have eq526845 : y = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq526844
  have eq526957 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op y x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1733 X0 y x X1
       have i₂ := eq526845
       grind)
    | exact superpose eq526845 eq1733
    | exact resolve eq1733 eq526845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526995 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq526845 eq526957
    | exact resolve eq526957 eq526845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526845 eq526957
  have eq527502 : ∀ X0 X1 X2 X4 : G, (k X1 X1) = (σ (M.op X2 (M.op (M.op X0 y) X4))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq4902 X2 x X4 X1
       have i₂ := eq526995 X0 x
       grind)
    | exact superpose eq526995 eq4902
    | exact resolve eq4902 eq526995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq527834 : ∀ X0 X1 X2 X4 : G, (σ (k X1 X1)) = (σ (M.op X2 (M.op (M.op X0 y) X4))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq11575 X2 x X4 X1
       have i₂ := eq526995 X0 x
       grind)
    | exact superpose eq526995 eq11575
    | exact resolve eq11575 eq526995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq528174 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq526995 x X0
       grind)
    | exact superpose eq526995 eq18
    | (have j1 := eq526995 x X0
       grind)
    | exact resolve eq18 eq526995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526995
  have eq528501 : ∀ X0 X2 X4 : G, (σ (M.op x y)) = (σ (M.op X2 (M.op (M.op X0 y) X4))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X2 X4
    first
    | exact superpose eq528174 eq527834
    | exact resolve eq527834 eq528174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527834
  have eq528741 : ∀ X0 X2 X4 : G, (M.op x y) = (σ (M.op X2 (M.op (M.op X0 y) X4))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X2 X4
    first
    | exact superpose eq528174 eq527502
    | exact resolve eq527502 eq528174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527502 eq528174
  have eq529175 : ∀ X0 X2 X4 : G, (σ (M.op x y)) = (σ (M.op X2 (M.op (M.op X0 y) X4))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X2 X4
    first
    | exact superpose eq20 eq528501
    | (have j0 := eq528501 X0 X2 X4
       grind)
    | exact resolve eq528501 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528501
  have eq529657 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq528741 eq529175
    | exact resolve eq529175 eq528741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528741 eq529175
  have eq529658 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq529657
  have eq530094 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq529658 eq28
    | exact resolve eq28 eq529658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq679543 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op y x) := by grind
  clear eq525028
  have eq679558 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq679543
       have r₂ := eq525964
       grind)
    | exact resolve eq679543 eq525964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525964 eq679543
  have eq680426 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1760
       have i₂ := eq679558
       grind)
    | exact superpose eq679558 eq1760
    | (have r₁ := eq1760
       have r₂ := eq679558
       grind)
    | exact resolve eq1760 eq679558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq680443 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1925 x X0
       have i₂ := eq679558
       grind)
    | exact superpose eq679558 eq1925
    | exact resolve eq1925 eq679558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq679558
  have eq680876 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq680426
  have eq680877 : y = (M.op y x) ∨ (k x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq680876
  have eq681161 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq680443 eq680877
    | exact resolve eq680877 eq680443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680877
  have eq685703 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq681161
       grind)
    | exact superpose eq681161 eq40
    | exact resolve eq40 eq681161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681161
  have eq685708 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq685703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq685703
    | exact resolve eq685703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685703
  have eq685712 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq685708
    | exact resolve eq685708 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685708
  have eq685716 : (M.op x y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq529658 eq685712
    | exact resolve eq685712 eq529658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685712
  have eq685723 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq685716 eq1564
    | exact resolve eq1564 eq685716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685716
  have eq685736 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq685723
       have i₂ := eq1703 sF2
       grind)
    | exact superpose eq1703 eq685723
    | exact resolve eq685723 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685723
  have eq685744 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq680443 eq685736
    | exact resolve eq685736 eq680443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685736
  have eq685745 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq685744
  have eq707741 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq685745 eq1733
    | exact resolve eq1733 eq685745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707792 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq680443 eq707741
    | exact resolve eq707741 eq680443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680443 eq707741
  have eq707831 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq685745 eq707792
    | exact resolve eq707792 eq685745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685745 eq707792
  have eq708074 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq707831 eq26
    | (have j1 := eq707831 (σ x)
       grind)
    | exact resolve eq26 eq707831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707831
  have eq708214 : y = (M.op y x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq708074
  have eq708255 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq708214
       grind)
    | exact superpose eq708214 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq708214
       grind)
    | exact resolve eq13 eq708214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708269 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op y x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1733 X0 y x X1
       have i₂ := eq708214
       grind)
    | exact superpose eq708214 eq1733
    | exact resolve eq1733 eq708214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708295 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq708255
  have eq708320 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq708214 eq708269
    | exact resolve eq708269 eq708214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708214 eq708269
  have eq708332 : (k x y) = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq708295
       have i₂ := eq1703 y
       grind)
    | exact superpose eq1703 eq708295
    | exact resolve eq708295 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708295
  have eq708846 : ∀ X0 X2 : G, (τ (τ (k X2 X2))) = (τ (M.op X0 y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | (have i₁ := eq3619 X2 x
       have i₂ := eq708320 X0 x
       grind)
    | exact superpose eq708320 eq3619
    | exact resolve eq3619 eq708320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3619
  have eq709778 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq708320 x X0
       grind)
    | exact superpose eq708320 eq18
    | (have j1 := eq708320 x X0
       grind)
    | exact resolve eq18 eq708320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq708320
  have eq710433 : ∀ X0 : G, (τ (τ (M.op x y))) = (τ (M.op X0 y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq709778 eq708846
    | exact resolve eq708846 eq709778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708846
  have eq711017 : ∀ X0 : G, (τ (M.op x y)) = (τ (M.op X0 y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq530094 eq710433
    | exact resolve eq710433 eq530094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710433
  have eq711370 : ∀ X0 : G, (M.op x y) = (τ (M.op X0 y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq530094 eq711017
    | exact resolve eq711017 eq530094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530094 eq711017
  have eq717627 : (M.op x y) = (τ (k y y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq711370 y
       have i₂ := eq1703 y
       grind)
    | exact superpose eq1703 eq711370
    | exact resolve eq711370 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711370
  have eq717710 : (M.op x y) = (τ (k x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq708332 eq717627
    | exact resolve eq717627 eq708332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708332 eq717627
  have eq721687 : (σ (M.op x y)) = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 (k x y)
       have i₂ := eq717710
       grind)
    | exact superpose eq717710 eq14
    | exact resolve eq14 eq717710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717710
  have eq721716 : (σ (M.op x y)) = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq721687
    | exact resolve eq721687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721687
  have eq721723 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq529658 eq721716
    | exact resolve eq721716 eq529658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721716
  have eq721734 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq721723
       grind)
    | exact superpose eq721723 eq40
    | exact resolve eq40 eq721723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq721723
  have eq721738 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq721734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq721734
    | exact resolve eq721734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq721734
  have eq721742 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq721738
    | exact resolve eq721738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq721738
  have eq721746 : (M.op x y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq529658 eq721742
    | exact resolve eq721742 eq529658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721742
  have eq721753 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq721746 eq1564
    | exact resolve eq1564 eq721746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq721746
  have eq721759 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq721753
  have eq721765 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq721759
       have i₂ := eq1703 sF2
       grind)
    | exact superpose eq1703 eq721759
    | exact resolve eq721759 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq721759
  have eq721774 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq709778 eq721765
    | exact resolve eq721765 eq709778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721765
  have eq721775 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq721774
  have eq721797 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq721775 eq1733
    | exact resolve eq1733 eq721775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq721848 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq709778 eq721797
    | exact resolve eq721797 eq709778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709778 eq721797
  have eq721888 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq721775 eq721848
    | exact resolve eq721848 eq721775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721775 eq721848
  have eq722139 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq721888 eq26
    | (have j1 := eq721888 (σ x)
       grind)
    | exact resolve eq26 eq721888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq721888
  have eq722278 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq722139
  have eq722388 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq722278 eq27
    | exact resolve eq27 eq722278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq722278
  have eq722533 : False := by grind
  exact eq722533

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pxy_x_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq9 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq24 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq24 X0 X1
       grind)
    | exact resolve eq13 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq26 X2 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq26 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq26 X3 X0
       grind)
    | exact superpose eq26 eq23
    | (have j1 := eq26 X3 X0
       grind)
    | exact resolve eq23 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq26
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq138 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq68 X1 X1 x X0
       grind)
    | (have r₁ := eq136 x X0
       have r₂ := eq68 X0 x x x
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq68 X1 X1 X1 x
       grind)
    | exact resolve eq136 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq136
  have eq412 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq138 (σ X0) (σ X1)
       grind)
    | exact superpose eq138 eq15
    | exact resolve eq15 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq412
    | exact resolve eq412 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq412
  have eq420 : False := by grind
  exact eq420

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_y_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq180 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq16 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 (M.op (M.op x x) x) x x
       have i₂ := eq16 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1560 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1630 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X2 X0
       have i₂ := eq1560 X0 X1
       grind)
    | exact superpose eq1560 eq181
    | exact resolve eq181 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1667 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 (M.op X1 X1)
       have i₂ := eq1560 (σ X0) X1
       grind)
    | exact superpose eq1560 eq478
    | exact resolve eq478 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1668 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq1560 (τ X0) X1
       grind)
    | exact superpose eq1560 eq34
    | exact resolve eq34 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1673 : ∀ X0 : G, (k x (τ (M.op X0 X0))) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op x x)
       have i₂ := eq1560 sF2 x
       grind)
    | exact superpose eq1560 eq90
    | exact resolve eq90 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1788 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478 X1 (M.op X2 X2)
       have i₂ := eq1630 (σ X1) X2 X0
       grind)
    | exact superpose eq1630 eq478
    | exact resolve eq478 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq1792 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op x y)) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (M.op X1 X1)
       have i₂ := eq1630 sF0 X1 x
       grind)
    | exact superpose eq1630 eq37
    | exact resolve eq37 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1795 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k y (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op X1 X1)
       have i₂ := eq1630 sF3 X1 x
       grind)
    | exact superpose eq1630 eq107
    | exact resolve eq107 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1796 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1795 X0 x
       have i₂ := eq1667 y x
       grind)
    | exact superpose eq1667 eq1795
    | exact resolve eq1795 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq1795
  have eq1799 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq1792 X0 x
       have i₂ := eq1668 sF1 x
       grind)
    | exact superpose eq1668 eq1792
    | exact resolve eq1792 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668 eq1792
  have eq1802 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1796 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1796
    | (have j0 := eq1796 X0
       grind)
    | exact resolve eq1796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1805 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq28 eq1799
    | exact resolve eq1799 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1799
  have eq1811 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1845 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1852 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1942 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1943 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1960 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1974 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1852 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq2018 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1802 X0
       have i₂ := eq1802 sF3
       grind)
    | exact superpose eq1802 eq1802
    | exact resolve eq1802 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq2143 : ∀ X0 X1 : G, (σ (M.op (M.op x y) (M.op x y))) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1805 x
       have i₂ := eq1630 X0 X1 x
       grind)
    | exact superpose eq1630 eq1805
    | exact resolve eq1805 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq1805
  have eq9830 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1943 X1
       have i₂ := eq1960 X1 X0
       grind)
    | exact superpose eq1960 eq1943
    | (have j0 := eq1943 X1
       have j1 := eq1960 X1 X1
       grind)
    | (have r₁ := eq1943 (M.op X1 X1)
       have r₂ := eq1960 (M.op X1 X1) X1
       grind)
    | exact resolve eq1943 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq1960
  have eq9860 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830
  have eq10179 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1974 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq10209 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (τ (M.op X0 X0)) ∨ (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10179 X2 (τ (M.op X1 X1))
       have i₂ := eq1788 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1788 eq10179
    | (have j0 := eq10179 X2 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq10179 X0 (τ (M.op X0 X0))
       have r₂ := eq1788 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq10179 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq10179
  have eq10214 : ∀ X1 X2 : G, (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq10209 x X1 X2
       grind)
    | (have r₁ := eq10209 x X1 X2
       have r₂ := eq2018 x X1
       grind)
    | (have r₁ := eq10209 X1 x X2
       have r₂ := eq2018 x X1
       grind)
    | exact resolve eq10209 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq10209
  have eq10217 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1845
       grind)
    | exact superpose eq1845 eq40
    | exact resolve eq40 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq10218 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10217
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10217
    | exact resolve eq10217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10217
  have eq10220 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq10218
    | exact resolve eq10218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218
  have eq10518 : ∀ X0 X1 X2 : G, (k (σ X1) (M.op X2 X2)) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (M.op X2 X2) X1
       have i₂ := eq10214 X2 X0
       grind)
    | exact superpose eq10214 eq38
    | exact resolve eq38 eq10214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq10524 : ∀ X1 X2 : G, (σ (M.op (M.op x y) (M.op x y))) = (k (σ X1) (M.op X2 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq10518 x X1 X2
       have i₂ := eq2143 X1 x
       grind)
    | exact superpose eq2143 eq10518
    | exact resolve eq10518 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143 eq10518
  have eq238141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10220 eq1846
    | exact resolve eq1846 eq10220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10220
  have eq238152 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq238141
       have r₂ := eq27
       grind)
    | exact resolve eq238141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238141
  have eq238234 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq238152 eq10214
    | exact resolve eq10214 eq238152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238152
  have eq238649 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq238234
    | exact resolve eq238234 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238234
  have eq238839 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq238649 y
       have j1 := eq9860 x y
       grind)
    | (have r₁ := eq238649 x
       have r₂ := eq9860 x y
       grind)
    | (have r₁ := eq238649 x
       have r₂ := eq9860 y y
       grind)
    | exact resolve eq238649 eq9860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238649
  have eq238962 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 y X0 X1
       have i₂ := eq238839
       grind)
    | exact superpose eq238839 eq180
    | exact resolve eq180 eq238839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238964 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y
       have i₂ := eq238839
       grind)
    | exact superpose eq238839 eq181
    | exact resolve eq181 eq238839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238839
  have eq239471 : ∀ X1 : G, y = (M.op X1 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq238964 eq238962
    | exact resolve eq238962 eq238964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238962 eq238964
  have eq246636 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq239471 x
       grind)
    | exact superpose eq239471 eq18
    | (have j1 := eq239471 x
       grind)
    | exact resolve eq18 eq239471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239471
  have eq246674 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq246636
  have eq246726 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq246674 eq1812
    | (have r₁ := eq1812
       have r₂ := eq246674
       grind)
    | exact resolve eq1812 eq246674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq246674
  have eq246753 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq246726
  have eq256469 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq246753 eq90
    | exact resolve eq90 eq246753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq246753
  have eq256492 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq256469
    | exact resolve eq256469 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256469
  have eq257762 : ∀ X0 : G, y = (k x y) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq256492 eq181
    | exact resolve eq181 eq256492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257791 : (k x (τ (σ y))) = (τ (M.op (σ x) (σ x))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq256492 eq1673
    | exact resolve eq1673 eq256492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq256492
  have eq258241 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq257791
    | exact resolve eq257791 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257791
  have eq258384 : (τ (σ y)) = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq257762 eq258241
    | exact resolve eq258241 eq257762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257762 eq258241
  have eq258474 : y = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq258384
    | exact resolve eq258384 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258384
  have eq258475 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq258474
  have eq258532 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1845
       have i₂ := eq258475
       grind)
    | exact superpose eq258475 eq1845
    | exact resolve eq1845 eq258475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845 eq258475
  have eq258540 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq258532
  have eq258559 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 y X0 X1
       have i₂ := eq258540
       grind)
    | exact superpose eq258540 eq180
    | exact resolve eq180 eq258540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258561 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y
       have i₂ := eq258540
       grind)
    | exact superpose eq258540 eq181
    | exact resolve eq181 eq258540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258540
  have eq259081 : ∀ X1 : G, y = (M.op X1 y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq258561 eq258559
    | exact resolve eq258559 eq258561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258559 eq258561
  have eq266872 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq259081 x
       grind)
    | exact superpose eq259081 eq18
    | (have j1 := eq259081 x
       grind)
    | exact resolve eq18 eq259081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq259081
  have eq266916 : y = (M.op x y) := by grind
  clear eq266872
  have eq266965 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq266916
       grind)
    | exact superpose eq266916 eq24
    | exact resolve eq24 eq266916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq266980 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1811
       have i₂ := eq266916
       grind)
    | exact superpose eq266916 eq1811
    | (have r₁ := eq1811
       have r₂ := eq266916
       grind)
    | exact resolve eq1811 eq266916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq267011 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq266980
  have eq267013 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq266965 eq20
    | exact resolve eq20 eq266965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267016 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq266965 eq15
    | exact resolve eq15 eq266965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266965
  have eq280112 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq267011 eq35
    | exact resolve eq35 eq267011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq267011
  have eq280122 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq280112
    | exact resolve eq280112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280112
  have eq280125 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq267013 eq280122
    | exact resolve eq280122 eq267013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280122
  have eq280136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq280125 eq1846
    | exact resolve eq1846 eq280125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq280125
  have eq280152 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq280136
  have eq324197 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq280152 eq10214
    | exact resolve eq10214 eq280152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10214 eq280152
  have eq324647 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq31 eq324197
    | exact resolve eq324197 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq324197
  have eq324846 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq324647 X0
       have i₂ := eq266916
       grind)
    | exact superpose eq266916 eq324647
    | exact resolve eq324647 eq266916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266916 eq324647
  have eq324996 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq324846 (M.op x y)
       have j1 := eq9860 x (M.op x y)
       grind)
    | (have r₁ := eq324846 x
       have r₂ := eq9860 x (M.op x y)
       grind)
    | (have r₁ := eq324846 x
       have r₂ := eq9860 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq324846 eq9860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860 eq324846
  have eq325111 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq324996 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq324996
       grind)
    | exact resolve eq13 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq324996 eq180
    | exact resolve eq180 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq325115 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq324996 eq181
    | exact resolve eq181 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq325222 : ∀ X0 : G, (σ (M.op x y)) = (k (σ X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq324996 eq10524
    | exact resolve eq10524 eq324996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10524 eq324996
  have eq325420 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq325111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325111
  have eq325554 : ∀ X0 : G, (σ (M.op x y)) = (k (σ X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq325222
    | (have j0 := eq325222 X0
       grind)
    | exact resolve eq325222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325222
  have eq325646 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq325115 eq325113
    | exact resolve eq325113 eq325115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325113
  have eq325647 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq325115 eq325420
    | exact resolve eq325420 eq325115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325115 eq325420
  have eq325751 : ∀ X0 : G, (σ y) = (k (σ X0) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq267013 eq325554
    | exact resolve eq325554 eq267013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325554
  have eq325887 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq325647 eq325751
    | exact resolve eq325751 eq325647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325647 eq325751
  have eq326082 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq325887 eq27
    | exact resolve eq27 eq325887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325887
  have eq326123 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq326082
       have r₂ := eq267013
       grind)
    | exact resolve eq326082 eq267013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267013 eq326082
  have eq326124 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq326123 eq26
    | exact resolve eq26 eq326123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq326271 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq326123 eq267016
    | exact resolve eq267016 eq326123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267016
  have eq326304 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq326271 eq14
    | exact resolve eq14 eq326271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326271
  have eq326308 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq326304 eq20
    | exact resolve eq20 eq326304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq326304
  have eq333062 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq325646 eq326124
    | exact resolve eq326124 eq325646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325646 eq326124
  have eq333085 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq326123 eq333062
    | exact resolve eq333062 eq326123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326123 eq333062
  have eq333086 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq333085
  have eq333852 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq333086 eq27
    | exact resolve eq27 eq333086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq333086
  have eq333935 : False := by grind
  exact eq333935
