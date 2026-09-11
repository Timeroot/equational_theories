import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxx_pyy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq217 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op X0 x)
       have i₂ := eq55 X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
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
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq237 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq220 eq236
    | exact resolve eq236 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq241 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq237 eq14
    | exact resolve eq14 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq241 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq241
    | exact resolve eq241 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq244 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq220 eq242
    | exact resolve eq242 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq381 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq220 eq217
    | exact resolve eq217 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq382 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq220 eq222
    | exact resolve eq222 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq537 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
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
  have eq538 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq220 eq537
    | exact resolve eq537 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq539 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq538 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq538
    | exact resolve eq538 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq540 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq220 eq539
    | exact resolve eq539 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq550 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq540 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq540 x
       grind)
    | exact resolve eq13 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq577 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq382 X0 X0
       have i₂ := eq559 X0
       grind)
    | exact superpose eq559 eq382
    | exact resolve eq382 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq80 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq818 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq827 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq807 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq807 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq807 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq838 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq3312 : (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq559 eq818
    | (have j0 := eq818 (M.op x (M.op x y))
       grind)
    | exact resolve eq818 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq3327 : (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq381 eq3312
    | exact resolve eq3312 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq3312
  have eq3328 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by grind
  clear eq3327
  have eq3335 : (σ (M.op x (M.op x y))) = (k (σ (M.op x (M.op x y))) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3328
       have i₂ := eq559 (σ (M.op x sF0))
       grind)
    | exact superpose eq559 eq3328
    | exact resolve eq3328 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq14085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq14094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14085
    | exact resolve eq14085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14085
  have eq14105 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq14094
       have r₂ := eq27
       grind)
    | exact resolve eq14094 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14094
  have eq14107 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14105
    | exact resolve eq14105 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14105
  have eq14114 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14107 eq55
    | exact resolve eq55 eq14107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14121 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq220 eq14114
    | exact resolve eq14114 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14114
  have eq14159 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14121 eq14107
    | exact resolve eq14107 eq14121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107 eq14121
  have eq14171 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq14159
  have eq14184 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14171 eq244
    | exact resolve eq244 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14171
  have eq14212 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14184
    | exact resolve eq14184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14184
  have eq14213 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14212
  have eq14220 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq14213
       grind)
    | exact superpose eq14213 eq55
    | exact resolve eq55 eq14213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq14227 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq220 eq14220
    | exact resolve eq14220 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14220
  have eq14272 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14213
       have i₂ := eq14227
       grind)
    | exact superpose eq14227 eq14213
    | exact resolve eq14213 eq14227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14213 eq14227
  have eq14284 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14272
  have eq14302 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14284 eq540
    | exact resolve eq540 eq14284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14284
  have eq14555 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14302 y
       grind)
    | exact superpose eq14302 eq18
    | (have j1 := eq14302 y
       grind)
    | exact resolve eq18 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14302
  have eq14591 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14555
  have eq14609 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14591 eq237
    | exact resolve eq237 eq14591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq14613 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14609
    | exact resolve eq14609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14609
  have eq14765 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14613 eq540
    | exact resolve eq540 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq14766 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14613 eq559
    | exact resolve eq559 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq14767 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 (M.op (σ x) (σ y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14613 eq577
    | exact resolve eq577 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq15008 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14591 eq14765
    | exact resolve eq14765 eq14591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14765
  have eq15040 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15008 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15008
  have eq20182 : (σ (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14613 eq3335
    | exact resolve eq3335 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335 eq14613
  have eq20224 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20182 eq14767
    | exact resolve eq14767 eq20182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14767
  have eq20239 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq20224
  have eq20346 : (M.op (σ x) (σ y)) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20239 eq14766
    | exact resolve eq14766 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14766 eq20239
  have eq20357 : (M.op (σ x) (σ y)) = (k (σ (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq20346
  have eq20378 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20357 eq20182
    | exact resolve eq20182 eq20357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20182 eq20357
  have eq20401 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq20378
  have eq20418 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20401 eq16
    | exact resolve eq16 eq20401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20401
  have eq20470 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14591 eq20418
    | exact resolve eq20418 eq14591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14591 eq20418
  have eq20517 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20470
  have eq20518 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq20517
    | exact resolve eq20517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20517
  have eq20749 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20518 eq15040
    | exact resolve eq15040 eq20518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15040 eq20518
  have eq20770 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20749
  have eq21464 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20770 y
       grind)
    | exact superpose eq20770 eq18
    | (have j1 := eq20770 y
       grind)
    | exact resolve eq18 eq20770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20770
  have eq21543 : x = (M.op x y) := by grind
  clear eq21464
  have eq21730 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21543 eq20
    | exact resolve eq20 eq21543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq21777 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21543 eq220
    | exact resolve eq220 eq21543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq21782 : (M.op x x) = (M.op (M.op x x) (σ y)) := by
    first
    | exact superpose eq21543 eq244
    | exact resolve eq244 eq21543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq21822 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21777
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21777
    | exact resolve eq21777 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21777
  have eq21867 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21730
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21730
    | exact resolve eq21730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21730
  have eq21868 : x = (M.op x x) := by
    first
    | exact superpose eq21543 eq21822
    | exact resolve eq21822 eq21543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21822
  have eq21906 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21867 eq26
    | exact resolve eq26 eq21867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq22187 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq21868
       grind)
    | exact superpose eq21868 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq21868
       grind)
    | exact resolve eq13 eq21868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22193 : x = (k x x) := by grind
  clear eq22187
  have eq22247 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq838 x x
       have i₂ := eq22193
       grind)
    | exact superpose eq22193 eq838
    | (have j0 := eq838 x x
       grind)
    | exact resolve eq838 eq22193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq22193
  have eq22250 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22247
  have eq22251 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22250
  have eq22264 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22251
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22251
    | exact resolve eq22251 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22251
  have eq22279 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21867 eq22264
    | exact resolve eq22264 eq21867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21867 eq22264
  have eq22386 : (M.op x (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22279 eq382
    | exact resolve eq382 eq22279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq22391 : (σ (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq22279 eq22386
    | exact resolve eq22386 eq22279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22279 eq22386
  have eq22405 : (σ (M.op x y)) = (M.op x x) := by
    first
    | exact superpose eq21543 eq22391
    | exact resolve eq22391 eq21543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21543 eq22391
  have eq22418 : x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq22405
       have i₂ := eq21868
       grind)
    | exact superpose eq21868 eq22405
    | exact resolve eq22405 eq21868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22405
  have eq22497 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq22418 eq21906
    | exact resolve eq21906 eq22418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906
  have eq26023 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq21782
       have i₂ := eq21868
       grind)
    | exact superpose eq21868 eq21782
    | exact resolve eq21782 eq21868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21782 eq21868
  have eq26024 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22497 eq26023
    | exact resolve eq26023 eq22497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22497 eq26023
  have eq26026 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq26024 eq27
    | exact resolve eq27 eq26024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq26024
  have eq26070 : False := by grind
  exact eq26070

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_pxy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
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
  have eq554 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
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
  have eq558 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq553
    | exact resolve eq553 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq677 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq685 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq3364 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq685
    | (have j0 := eq685 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq685 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq3379 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3364
    | (have j0 := eq3364 X0
       grind)
    | exact resolve eq3364 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq3364
  have eq3380 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq3410 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3380 eq259
    | exact resolve eq259 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3415 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3380 eq35
    | exact resolve eq35 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3380
  have eq3440 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq506 eq3415
    | exact resolve eq3415 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq3484 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3440
       grind)
    | exact superpose eq3440 eq16
    | exact resolve eq16 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3620 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3410
    | exact resolve eq3410 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3625 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3410 eq558
    | exact resolve eq558 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq3626 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3410 eq554
    | exact resolve eq554 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq3410
  have eq3698 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3620 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3620
    | exact resolve eq3620 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3992 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3698 X0
       grind)
    | exact superpose eq3698 eq15
    | exact resolve eq15 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698
  have eq4285 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq3992 X0
       grind)
    | exact superpose eq3992 eq55
    | exact resolve eq55 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4291 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq214 eq4285
    | exact resolve eq4285 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4794 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq519 eq3625
    | exact resolve eq3625 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq4825 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4794
       have i₂ := eq3620 (M.op x sF0)
       grind)
    | exact superpose eq3620 eq4794
    | exact resolve eq4794 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4794
  have eq4845 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq519 eq4825
    | exact resolve eq4825 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq29897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq29897
    | exact resolve eq29897 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29897
  have eq29910 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29898
       have r₂ := eq27
       grind)
    | exact resolve eq29898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29898
  have eq29914 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29910 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq29910
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq29910
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29910
       grind)
    | exact resolve eq12 eq29910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29910
  have eq29922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq29914
  have eq29923 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq29922
  have eq29934 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29923 eq99
    | exact resolve eq99 eq29923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq29923
  have eq29947 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq29934
  have eq30298 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29947 eq3484
    | exact resolve eq3484 eq29947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484 eq29947
  have eq30339 : x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq30298
    | exact resolve eq30298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30298
  have eq30340 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq30339
  have eq30354 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq30340
       grind)
    | exact superpose eq30340 eq55
    | exact resolve eq55 eq30340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq30355 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq411 y x
       have i₂ := eq30340
       grind)
    | exact superpose eq30340 eq411
    | exact resolve eq411 eq30340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30360 : (M.op y x) = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq214 eq30354
    | exact resolve eq30354 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30354
  have eq30883 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30340
       have i₂ := eq30360
       grind)
    | exact superpose eq30360 eq30340
    | exact resolve eq30340 eq30360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30340 eq30360
  have eq30893 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq30883
  have eq30947 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30893 eq30355
    | exact resolve eq30355 eq30893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30355 eq30893
  have eq30957 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq30947
  have eq30973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3440
       have i₂ := eq30957
       grind)
    | exact superpose eq30957 eq3440
    | exact resolve eq3440 eq30957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30986 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4291 x
       have i₂ := eq30957
       grind)
    | exact superpose eq30957 eq4291
    | exact resolve eq4291 eq30957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq30993 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq411 x x
       have i₂ := eq30957
       grind)
    | exact superpose eq30957 eq411
    | exact resolve eq411 eq30957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31001 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30986
       have i₂ := eq3992 x
       grind)
    | exact superpose eq3992 eq30986
    | exact resolve eq30986 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992 eq30986
  have eq31013 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30973
    | exact resolve eq30973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30973
  have eq31017 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq31001
       have i₂ := eq3440
       grind)
    | exact superpose eq3440 eq31001
    | exact resolve eq31001 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31001
  have eq32016 : (σ x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31017 eq31013
    | exact resolve eq31013 eq31017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31013
  have eq32032 : (σ x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq32016
  have eq32068 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32032 eq235
    | exact resolve eq235 eq32032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq32087 : (σ x) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32032 eq4845
    | exact resolve eq4845 eq32032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845
  have eq32114 : (σ x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32032 eq30993
    | exact resolve eq30993 eq32032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32032
  have eq32123 : (σ x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq32114
  have eq32139 : (σ (M.op x y)) = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq32087
    | exact resolve eq32087 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32087
  have eq32142 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq32068
    | exact resolve eq32068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32068
  have eq32146 : x = (τ (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq32139 eq28
    | exact resolve eq28 eq32139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32139
  have eq32280 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq32146
    | exact resolve eq32146 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32146
  have eq32304 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32142 eq229
    | exact resolve eq229 eq32142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32142
  have eq32306 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq32304
    | exact resolve eq32304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32304
  have eq32849 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3440
       have i₂ := eq32123
       grind)
    | exact superpose eq32123 eq3440
    | exact resolve eq3440 eq32123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440 eq32123
  have eq32950 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32306 eq30993
    | exact resolve eq30993 eq32306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30993
  have eq32961 : (M.op (σ x) (σ y)) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq32950
  have eq33308 : x = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30957
       have i₂ := eq32961
       grind)
    | exact superpose eq32961 eq30957
    | exact resolve eq30957 eq32961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30957 eq32961
  have eq33324 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq33308
  have eq33336 : x = (τ (σ (M.op x y))) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33324 eq28
    | exact resolve eq28 eq33324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33324
  have eq33471 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq33336
    | exact resolve eq33336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33336
  have eq33497 : x ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33471 eq27
    | exact resolve eq27 eq33471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33543 : (M.op x (M.op x y)) = (σ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32849 eq31017
    | exact resolve eq31017 eq32849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31017 eq32849
  have eq33562 : (M.op x (M.op x y)) = (σ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33543
  have eq33702 : (M.op (σ x) (σ y)) = (σ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33562 eq32306
    | exact resolve eq32306 eq33562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32306 eq33562
  have eq33711 : (M.op (σ x) (σ y)) = (σ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33702
  have eq33747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32280 eq33711
    | exact resolve eq33711 eq32280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32280 eq33711
  have eq33830 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33747
       have r₂ := eq33497
       grind)
    | exact resolve eq33747 eq33497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33497 eq33747
  have eq33832 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33830
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33830
    | exact resolve eq33830 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33830
  have eq33857 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33832 eq229
    | exact resolve eq229 eq33832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq33832
  have eq33870 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq33857
    | exact resolve eq33857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33857
  have eq34236 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33870 eq519
    | exact resolve eq519 eq33870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq33870
  have eq34692 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33471 eq34236
    | exact resolve eq34236 eq33471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33471 eq34236
  have eq34727 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34692
  have eq35124 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34727 y
       grind)
    | exact superpose eq34727 eq18
    | (have j1 := eq34727 y
       grind)
    | exact resolve eq18 eq34727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34727
  have eq35209 : x = (M.op x y) := by grind
  clear eq35124
  have eq35260 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq35209 eq20
    | exact resolve eq20 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq35307 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq35209 eq214
    | exact resolve eq214 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq35425 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq35307
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35307
    | exact resolve eq35307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35307
  have eq35471 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35260
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35260
    | exact resolve eq35260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35260
  have eq35476 : x = (M.op x x) := by
    first
    | exact superpose eq35209 eq35425
    | exact resolve eq35425 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35425
  have eq35514 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq35471 eq26
    | exact resolve eq26 eq35471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35721 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq35476
       grind)
    | exact resolve eq13 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35723 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq3626 x
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq3626
    | exact resolve eq3626 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626
  have eq35733 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq35721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35721
  have eq35742 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq35723
       have i₂ := eq3620 x
       grind)
    | exact superpose eq3620 eq35723
    | exact resolve eq35723 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq35723
  have eq35761 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq35742
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq35742
    | exact resolve eq35742 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35742
  have eq35780 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq35209 eq35761
    | exact resolve eq35761 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35761
  have eq35796 : x = (τ x) := by
    first
    | (have i₁ := eq35780
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq35780
    | exact resolve eq35780 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35780
  have eq35808 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq35796
       grind)
    | exact superpose eq35796 eq15
    | exact resolve eq15 eq35796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35796
  have eq35916 : x = (σ x) := by
    first
    | (have i₁ := eq35808
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35808
    | exact resolve eq35808 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35808
  have eq35943 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq35471 eq35916
    | exact resolve eq35916 eq35471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471 eq35916
  have eq36350 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq35943 eq35514
    | exact resolve eq35514 eq35943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35514
  have eq39245 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq35733 X0
       grind)
    | exact superpose eq35733 eq411
    | exact resolve eq411 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35733
  have eq39329 : ∀ X0 : G, (M.op x x) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | exact superpose eq35209 eq39245
    | exact resolve eq39245 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39245
  have eq39403 : ∀ X0 : G, x = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq39329 X0
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq39329
    | exact resolve eq39329 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39329
  have eq40542 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq411 (k X0 x) X0
       have i₂ := eq39403 X0
       grind)
    | exact superpose eq39403 eq411
    | exact resolve eq411 eq39403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq39403
  have eq40552 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq35209 eq40542
    | exact resolve eq40542 eq35209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35209 eq40542
  have eq40567 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq40552 X0
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq40552
    | exact resolve eq40552 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35476 eq40552
  have eq40614 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36350 eq40567
    | exact resolve eq40567 eq36350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36350 eq40567
  have eq40869 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq40614 eq27
    | exact resolve eq27 eq40614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40614
  have eq40892 : False := by grind
  exact eq40892

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq297 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq300 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq304 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq299 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq299 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq315 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq304 (σ X0)
       grind)
    | exact superpose eq304 eq15
    | exact resolve eq15 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq304 X0
       grind)
    | exact superpose eq304 eq315
    | exact resolve eq315 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq315
  have eq379 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq63
    | exact resolve eq63 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq301 (σ X1) (σ X0)
       grind)
    | exact superpose eq301 eq15
    | (have j1 := eq301 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq301 X1 (τ X0)
       grind)
    | exact superpose eq301 eq18
    | (have j1 := eq301 X1 (τ X0)
       grind)
    | exact resolve eq18 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq301
  have eq442 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq334 X1
       grind)
    | exact superpose eq334 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq425
  have eq728 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq433 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq433
    | exact resolve eq433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq791 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq728
    | (have j0 := eq728 X0 X1
       grind)
    | exact resolve eq728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1267 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq442 x y
       grind)
    | exact superpose eq442 eq16
    | (have j1 := eq442 x y
       grind)
    | exact resolve eq16 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq1348 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1267
       have i₂ := eq791 x y
       grind)
    | exact superpose eq791 eq1267
    | (have j1 := eq791 x y
       grind)
    | (have r₁ := eq1267
       have r₂ := eq791 x y
       grind)
    | exact resolve eq1267 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq1267
  have eq1349 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1348
  have eq1355 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1349
       grind)
    | exact superpose eq1349 eq63
    | exact resolve eq63 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq379 y
       have i₂ := eq1349
       grind)
    | exact superpose eq1349 eq379
    | exact resolve eq379 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1379 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1357
       grind)
    | exact superpose eq1357 eq16
    | exact resolve eq16 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1400 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1379
       have i₂ := eq1355
       grind)
    | exact superpose eq1355 eq1379
    | exact resolve eq1379 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq1379
  have eq1403 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1400
  have eq1404 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1403
  have eq1409 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq379 y
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq379
    | exact resolve eq379 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq1410 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq10
    | exact resolve eq10 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1456 : x = (M.op y y) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1410
    | exact resolve eq1410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1461 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1456
       grind)
    | exact superpose eq1456 eq63
    | exact resolve eq63 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1456
  have eq1488 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq16
    | exact resolve eq16 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1498 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq1461
       grind)
    | exact superpose eq1461 eq1488
    | exact resolve eq1488 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461 eq1488
  have eq1499 : False := by grind
  exact eq1499

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq314 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq317 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq318 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq322 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq316 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq316 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq316 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq333 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq322 (σ X0)
       grind)
    | exact superpose eq322 eq15
    | exact resolve eq15 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq333
    | exact resolve eq333 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq333
  have eq398 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq63
    | exact resolve eq63 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq318 (σ X1) (σ X0)
       grind)
    | exact superpose eq318 eq15
    | (have j1 := eq318 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq318 X1 (τ X0)
       grind)
    | exact superpose eq318 eq18
    | (have j1 := eq318 X1 (τ X0)
       grind)
    | exact resolve eq18 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq318
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq352 X1
       grind)
    | exact superpose eq352 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq447
  have eq757 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq455
    | exact resolve eq455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq757
    | (have j0 := eq757 X0 X1
       grind)
    | exact resolve eq757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1282 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464 x y
       grind)
    | exact superpose eq464 eq16
    | (have j1 := eq464 x y
       grind)
    | exact resolve eq16 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq1363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1282
       have i₂ := eq818 x y
       grind)
    | exact superpose eq818 eq1282
    | (have j1 := eq818 x y
       grind)
    | (have r₁ := eq1282
       have r₂ := eq818 x y
       grind)
    | exact resolve eq1282 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq1282
  have eq1364 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1363
  have eq1370 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1364
       grind)
    | exact superpose eq1364 eq63
    | exact resolve eq63 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1373 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq398 y
       have i₂ := eq1364
       grind)
    | exact superpose eq1364 eq398
    | exact resolve eq398 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1395 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1373
       grind)
    | exact superpose eq1373 eq16
    | exact resolve eq16 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1416 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1395
       have i₂ := eq1370
       grind)
    | exact superpose eq1370 eq1395
    | exact resolve eq1395 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq1395
  have eq1419 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1416
  have eq1420 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1419
  have eq1425 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq398 y
       have i₂ := eq1420
       grind)
    | exact superpose eq1420 eq398
    | exact resolve eq398 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq1426 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1420
       grind)
    | exact superpose eq1420 eq10
    | exact resolve eq10 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1472 : x = (M.op y y) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1426
    | exact resolve eq1426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1477 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq63
    | exact resolve eq63 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1472
  have eq1505 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq16
    | exact resolve eq16 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1515 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1505
       have i₂ := eq1477
       grind)
    | exact superpose eq1477 eq1505
    | exact resolve eq1505 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477 eq1505
  have eq1516 : False := by grind
  exact eq1516

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq40 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq33 X1 X0 X3
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq110 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq74 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq13 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq115 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq115
    | (have j0 := eq115 X0 X1
       grind)
    | exact resolve eq115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq466 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121
    | exact resolve eq121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121 x y
       grind)
    | exact superpose eq121 eq16
    | (have j1 := eq121 x y
       grind)
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq490 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq466
  have eq671 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq95 x X2 X0 X1
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq691 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq671 x X1 X0
       grind)
    | exact superpose eq671 eq9
    | exact resolve eq9 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq766 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq490
    | exact resolve eq490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq831 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq766 (τ X0) X1
       grind)
    | exact superpose eq766 eq18
    | (have j1 := eq766 (τ X0) X1
       grind)
    | exact resolve eq18 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1062 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq831 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq831
    | exact resolve eq831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq473
       have i₂ := eq1124 x y
       grind)
    | exact superpose eq1124 eq473
    | (have j1 := eq1124 (σ x) (σ y)
       grind)
    | (have r₁ := eq473
       have r₂ := eq1124 x y
       grind)
    | exact resolve eq473 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1964 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1963
  have eq2034 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2041 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq691 y y
       have i₂ := eq1964
       grind)
    | exact superpose eq1964 eq691
    | exact resolve eq691 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2051 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq473
       have i₂ := eq2034
       grind)
    | exact superpose eq2034 eq473
    | exact resolve eq473 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq2034
  have eq2056 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2051
  have eq2156 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2056
       have i₂ := eq2041
       grind)
    | exact superpose eq2041 eq2056
    | exact resolve eq2056 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq2056
  have eq2157 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2156
  have eq2158 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2157
  have eq2236 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2158
       grind)
    | exact superpose eq2158 eq40
    | exact resolve eq40 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2247 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq691 (σ y) (σ y)
       have i₂ := eq2158
       grind)
    | exact superpose eq2158 eq691
    | exact resolve eq691 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158
  have eq2263 : x = (k x y) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2236
    | exact resolve eq2236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2277 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq766 x y
       have i₂ := eq2263
       grind)
    | exact superpose eq2263 eq766
    | (have j0 := eq766 x y
       grind)
    | exact resolve eq766 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq2263
  have eq2419 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2247
       grind)
    | exact superpose eq2247 eq16
    | exact resolve eq16 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2540 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2419
       have i₂ := eq2277
       grind)
    | exact superpose eq2277 eq2419
    | exact resolve eq2419 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq2549 : x = (M.op y y) := by grind
  clear eq2540
  have eq2568 : x = (M.op x y) := by
    first
    | (have i₁ := eq691 y y
       have i₂ := eq2549
       grind)
    | exact superpose eq2549 eq691
    | exact resolve eq691 eq2549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq2549
  have eq2613 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2419
       have i₂ := eq2568
       grind)
    | exact superpose eq2568 eq2419
    | exact resolve eq2419 eq2568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419 eq2568
  have eq2622 : False := by grind
  exact eq2622

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq29
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq42
    | exact resolve eq42 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42
  have eq74 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq127 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq122 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq122 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq227 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq27 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq27
    | exact resolve eq27 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq227 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq227
    | exact resolve eq227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq244 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq229 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229
    | exact resolve eq229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq372 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq77 X0 (τ X0)
       grind)
    | exact superpose eq77 eq37
    | (have j1 := eq77 X0 (τ X0)
       grind)
    | exact resolve eq37 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq395 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq401 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | (have j0 := eq395 X0
       grind)
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq454 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 x
       have i₂ := eq75 x x
       grind)
    | exact superpose eq75 eq46
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq46 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq467 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq475 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq467 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq467
    | (have j0 := eq467 X0
       grind)
    | exact resolve eq467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq701 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq119
    | (have j0 := eq119 (σ X0) (σ X1)
       grind)
    | exact resolve eq119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq836 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq401 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq401
    | (have j0 := eq401 (σ X0)
       grind)
    | exact resolve eq401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq874 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq836 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq836
    | (have j0 := eq836 X0
       grind)
    | exact resolve eq836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq889 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq874 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq874
    | (have j0 := eq874 X0
       grind)
    | exact resolve eq874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1005 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq84 x X2 X0 X1
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1032 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq1005 x X1 X0
       grind)
    | exact superpose eq1005 eq9
    | exact resolve eq9 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1005 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1005 eq9
    | exact resolve eq9 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1073 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq1072
  have eq1076 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  have eq1101 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (σ (k (τ X0) (τ X0))) = (σ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq889 (τ X0)
       grind)
    | exact superpose eq889 eq37
    | (have j1 := eq889 (τ X0)
       grind)
    | exact resolve eq37 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1103 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) = (σ (k (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1101 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1101
    | (have j0 := eq1101 X0
       grind)
    | exact resolve eq1101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1107 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1103 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq1103
    | (have j0 := eq1103 X0
       grind)
    | exact resolve eq1103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1110 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1107 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1107
    | (have j0 := eq1107 X0
       grind)
    | exact resolve eq1107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1113 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1110 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1110
    | (have j0 := eq1110 X0
       grind)
    | exact resolve eq1110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1116 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1113 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1113
    | exact resolve eq1113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1154 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq1116
    | (have j0 := eq1116 X0
       grind)
    | exact resolve eq1116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1192 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131 (M.op X0 X0) X0
       have i₂ := eq244 X0
       grind)
    | exact superpose eq244 eq131
    | (have j0 := eq131 (M.op X0 X0) X0
       grind)
    | exact resolve eq131 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq1198 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 (τ X1) (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq131
    | (have j0 := eq131 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq131 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1213 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1216 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1198 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1198
    | (have j0 := eq1198 X0 X1
       grind)
    | exact resolve eq1198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1219 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1216 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1216
    | (have j0 := eq1216 X0 X1
       grind)
    | exact resolve eq1216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1221 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1222 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1221 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1221
    | (have j0 := eq1221 X0 X1
       grind)
    | exact resolve eq1221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1223 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1222 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1222
    | (have j0 := eq1222 X0 X1
       grind)
    | exact resolve eq1222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1224 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1223
    | (have j0 := eq1223 X0 X1
       grind)
    | exact resolve eq1223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1762 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    grind
  clear eq475
  have eq1774 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1762 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1762
    | (have j0 := eq1762 X0
       grind)
    | exact resolve eq1762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1912 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1224 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq1224
    | (have j0 := eq1224 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq1224 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1914 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1224 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq1224
    | (have j0 := eq1224 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq1224 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq1927 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq1912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq1999 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (σ (τ (k X0 X0))) = (σ (k (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1076 (τ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq1076
    | exact resolve eq1076 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2066 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1999 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq1999
    | (have j0 := eq1999 X0
       grind)
    | exact resolve eq1999 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2084 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2066 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq2066
    | (have j0 := eq2066 X0
       grind)
    | exact resolve eq2066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq2233 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1926 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1926
    | exact resolve eq1926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq2598 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1154 x
       have i₂ := eq405 x x
       grind)
    | exact superpose eq405 eq1154
    | (have j1 := eq405 X0 X0
       grind)
    | exact resolve eq1154 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq2651 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq4049 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1005 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1036 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1036 eq1005
    | exact resolve eq1005 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq4413 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X0 (M.op X1 X2)) X2 X2
       have i₂ := eq4049 X0 X1 X2
       grind)
    | exact superpose eq4049 eq20
    | exact resolve eq20 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4049
  have eq6254 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq1774 (τ X0)
       grind)
    | exact superpose eq1774 eq19
    | (have j1 := eq1774 (τ X0)
       grind)
    | exact resolve eq19 eq1774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774
  have eq6279 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6254 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq6254
    | (have j0 := eq6254 X0
       grind)
    | exact resolve eq6254 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254
  have eq6304 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6279 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6279
    | (have j0 := eq6279 X0
       grind)
    | exact resolve eq6279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279
  have eq6326 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6304 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq6304
    | (have j0 := eq6304 X0
       grind)
    | exact resolve eq6304 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304
  have eq6348 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6326 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6326
    | (have j0 := eq6326 X0
       grind)
    | exact resolve eq6326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326
  have eq6393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1224 (k X0 X0) X0
       have i₂ := eq6348 X0
       grind)
    | exact superpose eq6348 eq1224
    | (have j0 := eq1224 X0 X0
       have j1 := eq6348 X0
       grind)
    | exact resolve eq1224 eq6348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq6348
  have eq6418 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq7756 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq2084 X0
       grind)
    | exact superpose eq2084 eq37
    | (have j1 := eq2084 X0
       grind)
    | exact resolve eq37 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2084
  have eq7797 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7756 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq7756
    | (have j0 := eq7756 X0
       grind)
    | exact resolve eq7756 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756
  have eq7798 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq7797 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq11374 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1032 (σ X1) X0
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq1032
    | (have j1 := eq74 (σ X0) X0
       grind)
    | exact resolve eq1032 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11400 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq11401 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11400
  have eq11408 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11401 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11401
    | (have j0 := eq11401 X0
       grind)
    | exact resolve eq11401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11401
  have eq11476 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11408 X0
       grind)
    | exact superpose eq11408 eq46
    | (have j1 := eq11408 X0
       grind)
    | exact resolve eq46 eq11408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq11490 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2233 (σ X0)
       have i₂ := eq11408 X0
       grind)
    | exact superpose eq11408 eq2233
    | (have j1 := eq11408 X0
       grind)
    | exact resolve eq2233 eq11408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233 eq11408
  have eq11513 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11490
  have eq11516 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11513 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11513
    | (have j0 := eq11513 X0
       grind)
    | exact resolve eq11513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11513
  have eq11519 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11476 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11476
    | (have j0 := eq11476 X0
       grind)
    | exact resolve eq11476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11476
  have eq11970 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq11519 X0
       grind)
    | exact superpose eq11519 eq11
    | (have j1 := eq11519 X0
       grind)
    | exact resolve eq11 eq11519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11519
  have eq12146 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11970 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11970
    | (have j0 := eq11970 (τ X0)
       grind)
    | exact resolve eq11970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970
  have eq12240 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12146 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq12146
    | (have j0 := eq12146 X0
       grind)
    | exact resolve eq12146 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12250 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12240 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12240
    | (have j0 := eq12240 X0
       grind)
    | exact resolve eq12240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12240
  have eq12256 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12250 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq12250
    | (have j0 := eq12250 X0
       grind)
    | exact resolve eq12250 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12282 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq12256 X0
       grind)
    | exact superpose eq12256 eq11
    | (have j1 := eq12256 X0
       grind)
    | exact resolve eq11 eq12256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12256
  have eq12396 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12282 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12282
    | (have j0 := eq12282 X0
       grind)
    | exact resolve eq12282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12282
  have eq12410 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12396 X0
       have j1 := eq6418 X0
       grind)
    | (have r₁ := eq12396 X0
       have r₂ := eq6418 X0
       grind)
    | exact resolve eq12396 eq6418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418 eq12396
  have eq12699 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12410 (σ X0)
       grind)
    | exact superpose eq12410 eq15
    | exact resolve eq15 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12708 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq12410 (τ X0)
       grind)
    | exact superpose eq12410 eq38
    | exact resolve eq38 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12759 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12708 X0
       have i₂ := eq12410 X0
       grind)
    | exact superpose eq12410 eq12708
    | exact resolve eq12708 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708
  have eq12767 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12699 X0
       have i₂ := eq12410 X0
       grind)
    | exact superpose eq12410 eq12699
    | exact resolve eq12699 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12699
  have eq13085 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1073
       grind)
    | exact superpose eq1073 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1073
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1073
       grind)
    | exact resolve eq13 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq13104 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13085
  have eq13105 : (k x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13104
  have eq13124 : (k x y) = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13105
       have i₂ := eq12767 y
       grind)
    | exact superpose eq12767 eq13105
    | exact resolve eq13105 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13105
  have eq13198 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1032 (σ X0) (σ X0)
       have i₂ := eq12767 X0
       grind)
    | exact superpose eq12767 eq1032
    | exact resolve eq1032 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31859 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq701 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq701
    | (have j0 := eq701 (τ X0) (τ X1)
       grind)
    | exact resolve eq701 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq31962 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31859 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31859
    | (have j0 := eq31859 X0 X1
       grind)
    | exact resolve eq31859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31859
  have eq32014 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31962 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31962
    | (have j0 := eq31962 X0 X1
       grind)
    | exact resolve eq31962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31962
  have eq32063 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32014 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32014
    | (have j0 := eq32014 X0 X1
       grind)
    | exact resolve eq32014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32014
  have eq32106 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32063 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32063
    | (have j0 := eq32063 X0 X1
       grind)
    | exact resolve eq32063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32063
  have eq32142 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32106 X0 X1
       have i₂ := eq12767 (σ (τ X1))
       grind)
    | exact superpose eq12767 eq32106
    | (have j0 := eq32106 X0 X1
       grind)
    | exact resolve eq32106 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32106
  have eq32174 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32142 X0 X1
       have i₂ := eq12767 (τ X1)
       grind)
    | exact superpose eq12767 eq32142
    | (have j0 := eq32142 X0 X1
       grind)
    | exact resolve eq32142 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32142
  have eq32199 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (τ (M.op X1 X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32174 X0 X1
       have i₂ := eq12759 X1
       grind)
    | exact superpose eq12759 eq32174
    | (have j0 := eq32174 X0 X1
       grind)
    | exact resolve eq32174 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32174
  have eq32219 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32199 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq32199
    | (have j0 := eq32199 X0 X1
       grind)
    | exact resolve eq32199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32199
  have eq32233 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32219 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32219
    | (have j0 := eq32219 X0 X1
       grind)
    | exact resolve eq32219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32219
  have eq452184 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11374 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11374
    | exact resolve eq11374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374
  have eq452905 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq452184 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq452184
    | (have j0 := eq452184 X0 X0
       grind)
    | exact resolve eq452184 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq452184
  have eq453818 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq452905 X1 X0
       grind)
    | exact superpose eq452905 eq11
    | (have j1 := eq452905 X1 X1
       grind)
    | exact resolve eq11 eq452905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452905
  have eq454172 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq453818 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq453818
    | (have j0 := eq453818 X1 X1
       grind)
    | exact resolve eq453818 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453818
  have eq456543 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11516 X0
       have i₂ := eq454172 X1 (σ X0)
       grind)
    | exact superpose eq454172 eq11516
    | (have j0 := eq11516 X0
       have j1 := eq454172 X0 X0
       grind)
    | exact resolve eq11516 eq454172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11516
  have eq456559 : ∀ X0 X1 : G, (σ (τ X0)) ≠ X0 ∨ (M.op X0 X0) = (σ (τ X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0
       have i₂ := eq454172 X0 (τ X0)
       grind)
    | exact superpose eq454172 eq1927
    | (have j1 := eq454172 X1 (τ X0)
       grind)
    | (have r₁ := eq1927 (M.op X1 X1)
       have r₂ := eq454172 (σ (M.op (τ (M.op X1 X1)) (τ (M.op X1 X1)))) X1
       grind)
    | exact resolve eq1927 eq454172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927 eq454172
  have eq456601 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq456559 X0 X1
       grind)
    | (have r₁ := eq456559 X0 X1
       have r₂ := eq11 X0
       grind)
    | exact resolve eq456559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456559
  have eq456618 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456543 X0 X1
       have i₂ := eq12410 X0
       grind)
    | exact superpose eq12410 eq456543
    | (have j0 := eq456543 X0 X1
       grind)
    | exact resolve eq456543 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456543
  have eq456814 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456601 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq456601
    | (have j0 := eq456601 X0 X1
       grind)
    | exact resolve eq456601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456601
  have eq456828 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456618 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq456618
    | (have j0 := eq456618 X0 X1
       grind)
    | exact resolve eq456618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456618
  have eq456829 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq456828 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456828
  have eq456951 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456814 X0 X1
       have i₂ := eq12759 X0
       grind)
    | exact superpose eq12759 eq456814
    | (have j0 := eq456814 X0 X1
       grind)
    | exact resolve eq456814 eq12759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12759 eq456814
  have eq456965 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456829 X0 X1
       have i₂ := eq12767 X0
       grind)
    | exact superpose eq12767 eq456829
    | (have j0 := eq456829 X0 X1
       grind)
    | exact resolve eq456829 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456829
  have eq460785 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq456951 X1 X0
       grind)
    | exact superpose eq456951 eq19
    | (have j1 := eq456951 X1 X0
       grind)
    | exact resolve eq19 eq456951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq456951
  have eq463328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq456965 X1 (σ X0)
       grind)
    | exact superpose eq456965 eq15
    | (have j1 := eq456965 X1 (σ X0)
       grind)
    | exact resolve eq15 eq456965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456965
  have eq473054 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq460785 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq460785
    | (have j0 := eq460785 X1 (σ X0)
       grind)
    | exact resolve eq460785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460785
  have eq473791 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq473054 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq473054
    | (have j0 := eq473054 X0 X1
       grind)
    | exact resolve eq473054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473054
  have eq473953 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq473791 X0 X1
       have i₂ := eq12767 X0
       grind)
    | exact superpose eq12767 eq473791
    | (have j0 := eq473791 X0 X1
       grind)
    | exact resolve eq473791 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473791
  have eq474051 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq473953 X0 X1
       have i₂ := eq12767 X0
       grind)
    | exact superpose eq12767 eq473953
    | (have j0 := eq473953 X0 X1
       grind)
    | exact resolve eq473953 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473953
  have eq474113 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq474051 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq474051
    | (have j0 := eq474051 X0 X1
       grind)
    | exact resolve eq474051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474051
  have eq478170 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq474113 X0 X1
       grind)
    | exact superpose eq474113 eq10
    | (have j1 := eq474113 X0 X1
       grind)
    | exact resolve eq10 eq474113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474113
  have eq478705 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478170 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq478170
    | (have j0 := eq478170 X0 X1
       grind)
    | exact resolve eq478170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478170
  have eq497822 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq463328 x y
       grind)
    | exact superpose eq463328 eq16
    | (have j1 := eq463328 x y
       grind)
    | exact resolve eq16 eq463328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463328
  have eq500613 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq497822
       have i₂ := eq478705 y x
       grind)
    | exact superpose eq478705 eq497822
    | (have j1 := eq478705 y y
       grind)
    | (have r₁ := eq497822
       have r₂ := eq478705 y x
       grind)
    | exact resolve eq497822 eq478705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478705 eq497822
  have eq500616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq500613
  have eq500617 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq500616
  have eq500678 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13198 y
       have i₂ := eq500617
       grind)
    | exact superpose eq500617 eq13198
    | exact resolve eq13198 eq500617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500617
  have eq500796 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq500678
       have i₂ := eq12767 y
       grind)
    | exact superpose eq12767 eq500678
    | exact resolve eq500678 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500678
  have eq502004 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1213 y
       have i₂ := eq500796
       grind)
    | exact superpose eq500796 eq1213
    | (have r₁ := eq1213 y
       have r₂ := eq500796
       grind)
    | exact resolve eq1213 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq502024 : (σ x) = (σ y) ∨ (σ x) = (σ (k (k y y) y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2651 y
       have i₂ := eq500796
       grind)
    | exact superpose eq500796 eq2651
    | (have j0 := eq2651 y
       grind)
    | exact resolve eq2651 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651
  have eq502190 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq502024
       have i₂ := eq7798 y
       grind)
    | exact superpose eq7798 eq502024
    | exact resolve eq502024 eq7798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7798 eq502024
  have eq502193 : (σ x) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq502004
       have i₂ := eq12767 y
       grind)
    | exact superpose eq12767 eq502004
    | exact resolve eq502004 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502004
  have eq502194 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq502193
  have eq502209 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq502190
       have i₂ := eq12410 y
       grind)
    | exact superpose eq12410 eq502190
    | exact resolve eq502190 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502190
  have eq502210 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq502209
  have eq502215 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq502210
       have r₂ := eq502194
       grind)
    | exact resolve eq502210 eq502194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502194 eq502210
  have eq502958 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502215
       grind)
    | exact superpose eq502215 eq16
    | exact resolve eq16 eq502215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502215
  have eq502975 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq502958
       have r₂ := eq12767 x
       grind)
    | exact resolve eq502958 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502958
  have eq503019 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq27 X0 (M.op y y)
       have i₂ := eq502975
       grind)
    | exact superpose eq502975 eq27
    | exact resolve eq27 eq502975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503024 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (σ y) X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq34 (M.op y y) X0
       have i₂ := eq502975
       grind)
    | exact superpose eq502975 eq34
    | exact resolve eq34 eq502975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503340 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq502975
  have eq503539 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (k y (τ X0)) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq503024 X0
       have i₂ := eq34 y X0
       grind)
    | exact superpose eq34 eq503024
    | exact resolve eq503024 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq503024
  have eq503544 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (k (τ X0) y) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq503019 X0
       have i₂ := eq27 X0 y
       grind)
    | exact superpose eq27 eq503019
    | exact resolve eq503019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq503019
  have eq515201 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq503539 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq503539
    | exact resolve eq503539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503539
  have eq517127 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13198 y
       have i₂ := eq515201 X0
       grind)
    | exact superpose eq515201 eq13198
    | (have j1 := eq515201 X0
       grind)
    | exact resolve eq13198 eq515201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517156 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq515201 X0
       grind)
    | exact superpose eq515201 eq10
    | (have j1 := eq515201 X0
       grind)
    | exact resolve eq10 eq515201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515201
  have eq517693 : ∀ X0 : G, x = (M.op y y) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq517156 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq517156
    | (have j0 := eq517156 X0
       grind)
    | exact resolve eq517156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517156
  have eq518075 : ∀ X0 : G, x = (M.op x y) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1032 y y
       have i₂ := eq517693 X0
       grind)
    | exact superpose eq517693 eq1032
    | (have j1 := eq517693 X0
       grind)
    | exact resolve eq1032 eq517693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517693
  have eq521116 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq517127 X0
       grind)
    | exact superpose eq517127 eq16
    | (have j1 := eq517127 X0
       grind)
    | exact resolve eq16 eq517127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517127
  have eq523063 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k (M.op y y) X0) = (k y X0) ∨ (k (M.op y y) X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq521116 X0
       have i₂ := eq518075 X1
       grind)
    | exact superpose eq518075 eq521116
    | (have j0 := eq521116 X0
       have j1 := eq518075 X0
       grind)
    | exact resolve eq521116 eq518075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518075 eq521116
  have eq523065 : ∀ X0 X1 : G, (k (M.op y y) X0) = (k y X0) ∨ (k (M.op y y) X1) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq523063 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523063
  have eq527970 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq503544 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq503544
    | exact resolve eq503544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503544
  have eq528221 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq13198 y
       have i₂ := eq527970 X0
       grind)
    | exact superpose eq527970 eq13198
    | (have j1 := eq527970 X0
       grind)
    | exact resolve eq13198 eq527970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13198
  have eq528250 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq527970 X0
       grind)
    | exact superpose eq527970 eq10
    | (have j1 := eq527970 X0
       grind)
    | exact resolve eq10 eq527970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527970
  have eq528789 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq528250 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq528250
    | (have j0 := eq528250 X0
       grind)
    | exact resolve eq528250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528250
  have eq530650 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1032 y y
       have i₂ := eq528789 X0
       grind)
    | exact superpose eq528789 eq1032
    | (have j1 := eq528789 X0
       grind)
    | exact resolve eq1032 eq528789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq528789
  have eq530814 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32233 x y
       have i₂ := eq13124
       grind)
    | exact superpose eq13124 eq32233
    | (have j0 := eq32233 x y
       grind)
    | exact resolve eq32233 eq13124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq530832 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq530814
  have eq530855 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq530832
       have r₂ := eq500796
       grind)
    | exact resolve eq530832 eq500796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500796 eq530832
  have eq532794 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq528221 X0
       grind)
    | exact superpose eq528221 eq16
    | (have j1 := eq528221 X0
       grind)
    | exact resolve eq16 eq528221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528221
  have eq533025 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 y) = (k X0 (M.op y y)) ∨ (k X1 y) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq532794 X0
       have i₂ := eq530650 X1
       grind)
    | exact superpose eq530650 eq532794
    | (have j0 := eq532794 X0
       have j1 := eq530650 X0
       grind)
    | exact resolve eq532794 eq530650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530650 eq532794
  have eq533029 : ∀ X0 X1 : G, (k X0 y) = (k X0 (M.op y y)) ∨ (k X1 y) = (k X1 (M.op y y)) := by
    intro X0 X1
    first
    | (have j0 := eq533025 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533025
  have eq584133 : ∀ X0 : G, (k y X0) ≠ (k y X0) ∨ (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq523065 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523065
  have eq584134 : ∀ X0 : G, (k (M.op y y) X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq584133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584133
  have eq587084 : (M.op (M.op y y) (M.op y y)) = (k y (M.op y y)) := by
    first
    | (have i₁ := eq12410 (M.op y y)
       have i₂ := eq584134 (M.op y y)
       grind)
    | exact superpose eq584134 eq12410
    | exact resolve eq12410 eq584134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584134
  have eq594291 : ∀ X0 : G, y = (M.op y (M.op X0 (k y (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq4413 y (M.op y y) y X0
       have i₂ := eq587084
       grind)
    | exact superpose eq587084 eq4413
    | exact resolve eq4413 eq587084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4413 eq587084
  have eq656401 : ∀ X0 : G, (k X0 y) ≠ (k X0 y) ∨ (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq533029 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533029
  have eq656402 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq656401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656401
  have eq659874 : ∀ X0 : G, y = (M.op y (M.op X0 (k y y))) := by
    intro X0
    first
    | (have i₁ := eq594291 X0
       have i₂ := eq656402 y
       grind)
    | exact superpose eq656402 eq594291
    | exact resolve eq594291 eq656402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594291 eq656402
  have eq659884 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq659874 X0
       have i₂ := eq12410 y
       grind)
    | exact superpose eq12410 eq659874
    | exact resolve eq659874 eq12410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12410 eq659874
  have eq661717 : y = (M.op y y) := by
    first
    | (have i₁ := eq1005 y y y
       have i₂ := eq659884 (M.op y y)
       grind)
    | exact superpose eq659884 eq1005
    | exact resolve eq1005 eq659884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq659884
  have eq993950 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq530855
       grind)
    | exact superpose eq530855 eq16
    | exact resolve eq16 eq530855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994000 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq530855
       grind)
    | exact superpose eq530855 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq530855
       grind)
    | exact resolve eq13 eq530855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530855
  have eq994057 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq994000
  have eq994073 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq994057
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq994057
    | exact resolve eq994057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994057
  have eq994090 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq993950
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq993950
    | exact resolve eq993950 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993950
  have eq994103 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq994073
       have i₂ := eq12767 y
       grind)
    | exact superpose eq12767 eq994073
    | exact resolve eq994073 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994073
  have eq994112 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq994090
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq994090
    | exact resolve eq994090 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994090
  have eq994122 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq994103
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq994103
    | exact resolve eq994103 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994103
  have eq994130 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq994122
       have i₂ := eq12767 y
       grind)
    | exact superpose eq12767 eq994122
    | exact resolve eq994122 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994122
  have eq994131 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op y y) := by grind
  clear eq994130
  have eq994137 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq994131
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq994131
    | exact resolve eq994131 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994131
  have eq994143 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq994137
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq994137
    | exact resolve eq994137 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994137
  have eq997265 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq994143
       grind)
    | exact superpose eq994143 eq16
    | exact resolve eq16 eq994143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994143
  have eq997532 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq997265
       have r₂ := eq12767 x
       grind)
    | exact resolve eq997265 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997265
  have eq1000987 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq405 x y
       have i₂ := eq997532
       grind)
    | exact superpose eq997532 eq405
    | (have j0 := eq405 x y
       grind)
    | exact resolve eq405 eq997532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1000991 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32233 x y
       have i₂ := eq997532
       grind)
    | exact superpose eq997532 eq32233
    | (have j0 := eq32233 x y
       grind)
    | (have r₁ := eq32233 x y
       have r₂ := eq997532
       grind)
    | exact resolve eq32233 eq997532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32233 eq997532
  have eq1001344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq1000991
  have eq1001556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1001344
       have r₂ := eq503340
       grind)
    | exact resolve eq1001344 eq503340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503340 eq1001344
  have eq1001559 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1000987
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq1000987
    | exact resolve eq1000987 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000987
  have eq1001648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1001556
       have i₂ := eq661717
       grind)
    | exact superpose eq661717 eq1001556
    | exact resolve eq1001556 eq661717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661717 eq1001556
  have eq1001651 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1001559
       have r₂ := eq994112
       grind)
    | exact resolve eq1001559 eq994112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994112 eq1001559
  have eq1005862 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1001648
       grind)
    | exact superpose eq1001648 eq16
    | exact resolve eq16 eq1001648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001648
  have eq1009154 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1005862
       have i₂ := eq1001651
       grind)
    | exact superpose eq1001651 eq1005862
    | exact resolve eq1005862 eq1001651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001651 eq1005862
  have eq1009252 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1009154
  have eq1009253 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1009252
  have eq1011809 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1009253
       grind)
    | exact superpose eq1009253 eq16
    | exact resolve eq16 eq1009253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009253
  have eq1012076 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1011809
       have r₂ := eq12767 x
       grind)
    | exact resolve eq1011809 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011809
  have eq1012078 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1012076
       grind)
    | exact superpose eq1012076 eq16
    | exact resolve eq16 eq1012076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012121 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1012076
       grind)
    | exact superpose eq1012076 eq10
    | exact resolve eq10 eq1012076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012076
  have eq1012722 : x = y := by
    first
    | (have i₁ := eq1012121
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1012121
    | exact resolve eq1012121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012121
  have eq1012737 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1012078
       have i₂ := eq12767 x
       grind)
    | exact superpose eq12767 eq1012078
    | exact resolve eq1012078 eq12767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12767 eq1012078
  have eq1012903 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1012737
       have i₂ := eq1012722
       grind)
    | exact superpose eq1012722 eq1012737
    | exact resolve eq1012737 eq1012722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012722 eq1012737
  have eq1012904 : False := by grind
  exact eq1012904

/-- `Equation4487`: `x ◇ (y ◇ y) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4487.models_iff G M).mp hM
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X2) := by
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
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
  clear eq207
  have eq318 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (k (k x y) X0)) := by
    intro X0
    first
    | exact superpose eq99 eq35
    | exact resolve eq35 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq427
  have eq692 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X3) (M.op X1 X3))) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X1 X3) X3
       have i₂ := eq16 X0 X1 X3
       grind)
    | (have i₁ := eq16 X0 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 X1)
       have i₂ := eq16 (M.op X1 (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X0 X0)
       have i₂ := eq16 (M.op X3 (M.op X0 X0)) X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq693 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op x x)
       have i₂ := eq693 (M.op X1 (M.op x x))
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq718 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq694 eq16
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq719 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq718 x x
       have i₂ := eq708 x x
       grind)
    | exact superpose eq708 eq718
    | exact resolve eq718 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq732 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op x (M.op X0 X0)) X0 X1
       have i₂ := eq702 (M.op X0 X0)
       grind)
    | exact superpose eq702 eq16
    | exact resolve eq16 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x X1) (M.op x X1))) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op x X1) X1
       have i₂ := eq702 X1
       grind)
    | (have i₁ := eq16 X0 (M.op x y) y
       have i₂ := eq702 X1
       grind)
    | exact superpose eq702 eq16
    | exact resolve eq16 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq735 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq734 x X1
       have i₂ := eq708 x (M.op x X1)
       grind)
    | exact superpose eq708 eq734
    | exact resolve eq734 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq790 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq796 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq811 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq818 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq832 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq849 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1 x
       have i₂ := eq708 x X0
       grind)
    | exact superpose eq708 eq796
    | (have j0 := eq796 X1 X1 x
       grind)
    | exact resolve eq796 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq854 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq832 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq832 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq832 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq913 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq735 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) y)
       have r₂ := eq735 (M.op (M.op x y) y)
       grind)
    | exact resolve eq28 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq920 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq913 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq930 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq920 eq35
    | exact resolve eq35 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq920
  have eq944 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq930 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq930
    | exact resolve eq930 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq991 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq944 eq819
    | (have j0 := eq819 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq819 (σ (M.op (M.op x y) y))
       have r₂ := eq944 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq819 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq944
  have eq1004 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq991
  have eq2784 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq803
       grind)
    | exact superpose eq803 eq41
    | exact resolve eq41 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2785 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2784
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2784
    | exact resolve eq2784 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2787 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2785
    | exact resolve eq2785 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785
  have eq12150 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1) X1
       have i₂ := eq849 X0 X1
       grind)
    | exact superpose eq849 eq11
    | (have j0 := eq11 X1 X1
       have j1 := eq849 X1 X1
       grind)
    | exact resolve eq11 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12162 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq22509 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq1004 eq708
    | exact resolve eq708 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22518 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq1004 eq696
    | exact resolve eq696 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq22522 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1004 eq732
    | exact resolve eq732 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22525 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq1004 eq22518
    | exact resolve eq22518 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22518
  have eq22537 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq22525 x x
       have i₂ := eq708 x x
       grind)
    | exact superpose eq708 eq22525
    | exact resolve eq22525 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22525
  have eq22578 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq22537 eq15
    | exact resolve eq15 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2787 eq811
    | exact resolve eq811 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25111 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25103
       have r₂ := eq27
       grind)
    | exact resolve eq25103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25103
  have eq25118 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25111 eq218
    | exact resolve eq218 eq25111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq25111
  have eq25158 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq25118
    | exact resolve eq25118 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25118
  have eq25163 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq25158
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq25158
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq25158
       have r₂ := eq13 x y
       grind)
    | exact resolve eq25158 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25158
  have eq25488 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25163 eq200
    | exact resolve eq200 eq25163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq25163
  have eq25533 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq25488
    | exact resolve eq25488 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25539 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq854 y x
       grind)
    | (have r₁ := eq25533
       have r₂ := eq854 y x
       grind)
    | exact resolve eq25533 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq25533
  have eq25542 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq25539
       have r₂ := eq13 x y
       grind)
    | exact resolve eq25539 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25539
  have eq25546 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq803
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq803
    | exact resolve eq803 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq25548 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq41
    | exact resolve eq41 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq25549 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq849 x y
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq849
    | (have j0 := eq849 y y
       grind)
    | exact resolve eq849 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25550 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25549
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25549
    | exact resolve eq25549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25549
  have eq25551 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq25548
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25548
    | exact resolve eq25548 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25548
  have eq25558 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25551 eq2787
    | exact resolve eq2787 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787
  have eq25561 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25551 eq811
    | exact resolve eq811 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq25565 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25551 eq849
    | (have j0 := eq849 (σ y) (σ y)
       grind)
    | exact resolve eq849 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq25566 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq25565
    | exact resolve eq25565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25565
  have eq25572 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25561 eq25566
    | exact resolve eq25566 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25566
  have eq25600 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq732 y y
       have i₂ := eq25546
       grind)
    | exact superpose eq25546 eq732
    | exact resolve eq732 eq25546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25603 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25546 eq25600
    | exact resolve eq25600 eq25546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25546 eq25600
  have eq25646 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq732 y y
       have i₂ := eq25558
       grind)
    | exact superpose eq25558 eq732
    | exact resolve eq732 eq25558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25649 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25558 eq25646
    | exact resolve eq25646 eq25558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25558 eq25646
  have eq25675 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ y) X1))) = (M.op (M.op X2 (σ y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq25561 eq692
    | exact resolve eq692 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25682 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq25561 eq16
    | exact resolve eq16 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25692 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25561 eq732
    | exact resolve eq732 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25695 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq25561 eq25692
    | exact resolve eq25692 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25692
  have eq25699 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq25561 eq25682
    | exact resolve eq25682 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25561 eq25682
  have eq25702 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 (σ y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq25675 x X1 X2
       have i₂ := eq708 x (M.op sF3 X1)
       grind)
    | exact superpose eq708 eq25675
    | exact resolve eq25675 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25675
  have eq25709 : ∀ X1 X2 : G, (σ y) = (M.op (M.op X2 (σ y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq25695 eq25702
    | exact resolve eq25702 eq25695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25695 eq25702
  have eq25712 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq25699 eq25709
    | exact resolve eq25709 eq25699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25699 eq25709
  have eq25881 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25603 eq22509
    | exact resolve eq22509 eq25603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25883 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25603 eq22537
    | exact resolve eq22537 eq25603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25603
  have eq25909 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq25883
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25883
    | exact resolve eq25883 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25883
  have eq25911 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq25881 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25881
    | (have j0 := eq25881 X0
       grind)
    | exact resolve eq25881 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25881
  have eq25974 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25909 eq25911
    | exact resolve eq25911 eq25909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25911
  have eq26028 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq25909
       grind)
    | exact superpose eq25909 eq695
    | exact resolve eq695 eq25909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25909
  have eq26544 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25649 eq22509
    | exact resolve eq22509 eq25649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26546 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25649 eq22537
    | exact resolve eq22537 eq25649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25649
  have eq26572 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26546
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26546
    | exact resolve eq26546 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26546
  have eq26574 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26544 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26544
    | (have j0 := eq26544 X0
       grind)
    | exact resolve eq26544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26544
  have eq26637 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26572 eq26574
    | exact resolve eq26574 eq26572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26574
  have eq26691 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq26572
       grind)
    | exact superpose eq26572 eq695
    | exact resolve eq695 eq26572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26572
  have eq28168 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25974 eq26
    | (have j1 := eq25974 (σ x)
       grind)
    | exact resolve eq26 eq25974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28308 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq28168
       grind)
    | exact superpose eq28168 eq695
    | exact resolve eq695 eq28168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28168
  have eq28553 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X1 (M.op X0 y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X1 y
       have i₂ := eq26028 y X0
       grind)
    | (have i₁ := eq708 X1 y
       have i₂ := eq26028 X0 y
       grind)
    | exact superpose eq26028 eq708
    | exact resolve eq708 eq26028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28590 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq26028 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq26028 X0 x
       grind)
    | exact superpose eq26028 eq18
    | (have j1 := eq26028 x X0
       grind)
    | exact resolve eq18 eq26028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28682 : ∀ X0 : G, (M.op X0 y) = (τ (M.op X0 y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22578
       have i₂ := eq26028 sF0 x
       grind)
    | (have i₁ := eq22578
       have i₂ := eq26028 X0 sF0
       grind)
    | exact superpose eq26028 eq22578
    | exact resolve eq22578 eq26028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26028
  have eq28796 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq28590 eq28553
    | (have j0 := eq28553 x X1
       grind)
    | exact resolve eq28553 eq28590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28553
  have eq28985 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq28590 eq28796
    | exact resolve eq28796 eq28590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28590 eq28796
  have eq32697 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26637 eq26
    | (have j1 := eq26637 (σ x)
       grind)
    | exact resolve eq26 eq26637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26637
  have eq32837 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq32697
       grind)
    | exact superpose eq32697 eq695
    | exact resolve eq695 eq32697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32697
  have eq33417 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1004
       have i₂ := eq26691 sF0 x
       grind)
    | (have i₁ := eq1004
       have i₂ := eq26691 X0 sF0
       grind)
    | exact superpose eq26691 eq1004
    | exact resolve eq1004 eq26691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33479 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22522
       have i₂ := eq26691 sF0 x
       grind)
    | (have i₁ := eq22522
       have i₂ := eq26691 X0 sF0
       grind)
    | exact superpose eq26691 eq22522
    | exact resolve eq22522 eq26691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33543 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq26691 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq26691 X0 x
       grind)
    | exact superpose eq26691 eq18
    | (have j1 := eq26691 x X0
       grind)
    | exact resolve eq18 eq26691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26691
  have eq33790 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq33543 eq33479
    | (have j0 := eq33479 x
       grind)
    | exact resolve eq33479 eq33543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33479
  have eq33851 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq33543 eq33417
    | (have j0 := eq33417 x
       grind)
    | exact resolve eq33417 eq33543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33417 eq33543
  have eq33976 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq33790
    | exact resolve eq33790 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33790
  have eq34007 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq33851
    | exact resolve eq33851 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33851
  have eq34065 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq33976 eq34007
    | exact resolve eq34007 eq33976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33976 eq34007
  have eq34146 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  clear eq34065
  have eq38172 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq28308 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq28308 X0 x
       grind)
    | exact superpose eq28308 eq18
    | (have j1 := eq28308 x X0
       grind)
    | exact resolve eq18 eq28308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42479 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318 y
       have i₂ := eq12162 x y
       grind)
    | exact superpose eq12162 eq318
    | (have j1 := eq12162 x y
       grind)
    | exact resolve eq318 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq42491 : (τ (M.op (M.op x y) y)) = (k (k x y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 sF3
       have i₂ := eq12162 sF2 sF3
       grind)
    | exact superpose eq12162 eq604
    | (have j1 := eq12162 (σ x) (σ y)
       grind)
    | exact resolve eq604 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq12162
  have eq42798 : (τ (M.op (M.op x y) y)) = (k (k x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq42491
    | exact resolve eq42491 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42491
  have eq42810 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq42479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42479
    | exact resolve eq42479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42479
  have eq42980 : (k x y) = (τ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42798
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq42798
    | exact resolve eq42798 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42798
  have eq42992 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25551 eq42810
    | exact resolve eq42810 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42810
  have eq43047 : (k x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22578 eq42980
    | exact resolve eq42980 eq22578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42980
  have eq43049 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22537 eq42992
    | exact resolve eq42992 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42992
  have eq43074 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43047
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq43047
    | exact resolve eq43047 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43047
  have eq43076 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25551 eq43049
    | exact resolve eq43049 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43049
  have eq43092 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25551 eq43074
    | exact resolve eq43074 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25551 eq43074
  have eq43093 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq43092
  have eq43094 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43076
       have i₂ := eq25542
       grind)
    | exact superpose eq25542 eq43076
    | exact resolve eq43076 eq25542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25542 eq43076
  have eq43095 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq43094
  have eq43107 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25572 eq43093
    | exact resolve eq43093 eq25572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25572 eq43093
  have eq43108 : y = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25550 eq43095
    | exact resolve eq43095 eq25550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25550 eq43095
  have eq43129 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ y) X1))) = (M.op (M.op X2 (σ y)) X1) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq43107 eq692
    | exact resolve eq692 eq43107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43136 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq43107 eq16
    | exact resolve eq16 eq43107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43146 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43107 eq732
    | exact resolve eq732 eq43107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43149 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq43107 eq43146
    | exact resolve eq43146 eq43107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43146
  have eq43153 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq43107 eq43136
    | exact resolve eq43136 eq43107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43107 eq43136
  have eq43156 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 (σ y)) X1) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1 X2
    first
    | (have i₁ := eq43129 x X1 X2
       have i₂ := eq708 x (M.op sF3 X1)
       grind)
    | exact superpose eq708 eq43129
    | exact resolve eq43129 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43129
  have eq43163 : ∀ X1 X2 : G, (σ y) = (M.op (M.op X2 (σ y)) X1) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq43149 eq43156
    | exact resolve eq43156 eq43149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43149 eq43156
  have eq43166 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq43153 eq43163
    | exact resolve eq43163 eq43153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43153 eq43163
  have eq43221 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq732 y y
       have i₂ := eq43108
       grind)
    | exact superpose eq43108 eq732
    | exact resolve eq732 eq43108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq43224 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq43108 eq43221
    | exact resolve eq43221 eq43108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43108 eq43221
  have eq43881 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq43224 eq22509
    | exact resolve eq22509 eq43224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq43883 : y = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq43224 eq22537
    | exact resolve eq22537 eq43224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43224
  have eq43926 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq43883
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43883
    | exact resolve eq43883 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43883
  have eq43928 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq43881 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43881
    | (have j0 := eq43881 X0
       grind)
    | exact resolve eq43881 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43881
  have eq43991 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq43926 eq43928
    | exact resolve eq43928 eq43926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43928
  have eq44085 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq43926
       grind)
    | exact superpose eq43926 eq695
    | exact resolve eq695 eq43926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43926
  have eq45629 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43991 eq26
    | (have j1 := eq43991 (σ x)
       grind)
    | exact resolve eq26 eq43991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43991
  have eq45771 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq45629
       grind)
    | exact superpose eq45629 eq695
    | exact resolve eq695 eq45629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45629
  have eq46929 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1004
       have i₂ := eq44085 sF0 x
       grind)
    | (have i₁ := eq1004
       have i₂ := eq44085 X0 sF0
       grind)
    | exact superpose eq44085 eq1004
    | exact resolve eq1004 eq44085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46991 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (M.op X0 y)) (σ (M.op X0 y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22522
       have i₂ := eq44085 sF0 x
       grind)
    | (have i₁ := eq22522
       have i₂ := eq44085 X0 sF0
       grind)
    | exact superpose eq44085 eq22522
    | exact resolve eq22522 eq44085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47075 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq44085 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq44085 X0 x
       grind)
    | exact superpose eq44085 eq18
    | (have j1 := eq44085 x X0
       grind)
    | exact resolve eq18 eq44085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47169 : ∀ X0 : G, (M.op X0 y) = (τ (M.op X0 y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22578
       have i₂ := eq44085 sF0 x
       grind)
    | (have i₁ := eq22578
       have i₂ := eq44085 X0 sF0
       grind)
    | exact superpose eq44085 eq22578
    | exact resolve eq22578 eq44085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22578 eq44085
  have eq47365 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq47075 eq46991
    | (have j0 := eq46991 x
       grind)
    | exact resolve eq46991 eq47075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46991
  have eq47426 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq47075 eq46929
    | (have j0 := eq46929 x
       grind)
    | exact resolve eq46929 eq47075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46929
  have eq47555 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq47365
    | exact resolve eq47365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47365
  have eq47586 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq47426
    | exact resolve eq47426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47426
  have eq47648 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq47555 eq47586
    | exact resolve eq47586 eq47555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47555 eq47586
  have eq47660 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq47648
       have r₂ := eq34146
       grind)
    | exact resolve eq47648 eq34146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34146 eq47648
  have eq47677 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq47660 eq29
    | exact resolve eq29 eq47660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq53245 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq45771 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq45771 X0 x
       grind)
    | exact superpose eq45771 eq18
    | (have j1 := eq45771 x X0
       grind)
    | exact resolve eq18 eq45771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45771
  have eq67004 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq32837 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq32837 X0 x
       grind)
    | exact superpose eq32837 eq18
    | (have j1 := eq32837 x X0
       grind)
    | exact resolve eq18 eq32837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32837
  have eq67248 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53245 eq67004
    | (have j0 := eq67004 X0
       have j1 := eq53245 X0
       grind)
    | exact resolve eq67004 eq53245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53245 eq67004
  have eq67396 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq47660 eq67248
    | exact resolve eq67248 eq47660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67248
  have eq67524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ y) X1))) = (M.op (M.op X2 (M.op x y)) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq67396 eq692
    | exact resolve eq692 eq67396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq67528 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq67396 eq708
    | exact resolve eq708 eq67396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67637 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq47660 eq67528
    | exact resolve eq67528 eq47660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67528
  have eq67640 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 (M.op x y)) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq67524 x X1 X2
       have i₂ := eq708 x (M.op sF3 X1)
       grind)
    | exact superpose eq708 eq67524
    | exact resolve eq67524 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67524
  have eq67681 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq67396 eq67637
    | exact resolve eq67637 eq67396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67637
  have eq67683 : ∀ X1 X2 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op X2 (M.op x y)) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq47660 eq67640
    | exact resolve eq67640 eq47660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67640
  have eq67702 : ∀ X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op x y)) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq67396 eq67683
    | exact resolve eq67683 eq67396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67396 eq67683
  have eq67708 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq67681 eq67702
    | exact resolve eq67702 eq67681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67681 eq67702
  have eq68260 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67708 eq22537
    | exact resolve eq22537 eq67708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22537 eq67708
  have eq68398 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq68260
    | exact resolve eq68260 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68260
  have eq68399 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq68398
  have eq91706 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25712 eq47169
    | exact resolve eq47169 eq25712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25712 eq47169
  have eq91855 : y = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq91706
    | exact resolve eq91706 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91706
  have eq91856 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq91855
  have eq96021 : (σ y) = (τ (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43166 eq28682
    | exact resolve eq28682 eq43166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28682 eq43166
  have eq96167 : y = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq96021
    | exact resolve eq96021 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq96021
  have eq96168 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ y = (σ y) := by grind
  clear eq96167
  have eq99842 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq91856 eq708
    | exact resolve eq708 eq91856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq91856
  have eq99871 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq47075 eq99842
    | exact resolve eq99842 eq47075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99842
  have eq105353 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq99871 eq26
    | (have j1 := eq99871 (σ x)
       grind)
    | exact resolve eq26 eq99871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99871
  have eq105476 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq105353 eq719
    | exact resolve eq719 eq105353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq105353
  have eq105488 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq105476
    | exact resolve eq105476 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105476
  have eq105494 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq47075 eq105488
    | exact resolve eq105488 eq47075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47075 eq105488
  have eq105495 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq105494
  have eq105507 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq105495 eq27
    | exact resolve eq27 eq105495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105495
  have eq105527 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq105507
       have r₂ := eq47660
       grind)
    | exact resolve eq105507 eq47660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47660 eq105507
  have eq105530 : x = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq105527 eq30
    | exact resolve eq30 eq105527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq105645 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq105527 eq96168
    | exact resolve eq96168 eq105527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96168 eq105527
  have eq105648 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq105645
  have eq105657 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq28985 eq105648
    | exact resolve eq105648 eq28985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28985 eq105648
  have eq105727 : y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47677 eq105530
    | exact resolve eq105530 eq47677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47677 eq105530
  have eq105786 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq105727
       grind)
    | exact superpose eq105727 eq18
    | exact resolve eq18 eq105727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105787 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq105727
       grind)
    | exact superpose eq105727 eq24
    | exact resolve eq24 eq105727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq105813 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq735 x
       have i₂ := eq105727
       grind)
    | exact superpose eq105727 eq735
    | exact resolve eq735 eq105727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105928 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38172 X0
       have i₂ := eq105727
       grind)
    | exact superpose eq105727 eq38172
    | exact resolve eq38172 eq105727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38172
  have eq105965 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq105928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105928
  have eq106673 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105786 eq25974
    | exact resolve eq25974 eq105786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25974
  have eq106689 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq106673
  have eq106701 : (σ y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq105657 eq106689
    | exact resolve eq106689 eq105657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105657 eq106689
  have eq108674 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105965 eq26
    | (have j1 := eq105965 (σ x)
       grind)
    | exact resolve eq26 eq105965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105965
  have eq108796 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq109765 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 x x
       have i₂ := eq106701
       grind)
    | exact superpose eq106701 eq695
    | exact resolve eq695 eq106701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq106701
  have eq111994 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105813 eq28308
    | exact resolve eq28308 eq105813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28308 eq105813
  have eq112089 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq111994 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111994
  have eq112135 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq105727 eq112089
    | exact resolve eq112089 eq105727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105727 eq112089
  have eq112206 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq109765 eq112135
    | (have j0 := eq112135 X0
       have j1 := eq109765 X0 (M.op x y)
       grind)
    | exact resolve eq112135 eq109765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109765 eq112135
  have eq114691 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112206 eq105786
    | exact resolve eq105786 eq112206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105786
  have eq114696 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112206 eq26
    | (have j1 := eq112206 (σ x)
       grind)
    | exact resolve eq26 eq112206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112206
  have eq114799 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq114691
  have eq114848 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108674 eq114696
    | exact resolve eq114696 eq108674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108674 eq114696
  have eq114910 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114799 eq114848
    | exact resolve eq114848 eq114799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114799 eq114848
  have eq114935 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq114910
       have r₂ := eq108796
       grind)
    | exact resolve eq114910 eq108796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108796 eq114910
  have eq114947 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114935 eq27
    | exact resolve eq27 eq114935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114956 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114935 eq68399
    | exact resolve eq68399 eq114935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68399 eq114935
  have eq115997 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114956 eq105787
    | exact resolve eq105787 eq114956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105787 eq114956
  have eq116059 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq115997
  have eq116140 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116059
       have r₂ := eq114947
       grind)
    | exact resolve eq116059 eq114947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116059
  have eq116303 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq116140
    | exact resolve eq116140 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116140
  have eq116441 : x = (M.op x y) := by
    first
    | (have r₁ := eq116303
       have r₂ := eq114947
       grind)
    | exact resolve eq116303 eq114947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114947 eq116303
  have eq116530 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq116441
       grind)
    | exact superpose eq116441 eq18
    | exact resolve eq18 eq116441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq116531 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq116441
       grind)
    | exact superpose eq116441 eq22
    | exact resolve eq22 eq116441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq116441
  have eq116678 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq116531 eq20
    | exact resolve eq20 eq116531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116531
  have eq117381 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq116530 eq735
    | exact resolve eq735 eq116530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq117399 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq116530 eq1004
    | exact resolve eq1004 eq116530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq117461 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq116530 eq22522
    | exact resolve eq22522 eq116530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22522 eq116530
  have eq117526 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq117461
    | exact resolve eq117461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117461
  have eq117587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq117399
    | exact resolve eq117399 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq117399
  have eq117601 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq116678 eq117526
    | exact resolve eq117526 eq116678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117526
  have eq117650 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq116678 eq117587
    | exact resolve eq117587 eq116678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117587
  have eq117673 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq117601 eq117650
    | exact resolve eq117650 eq117601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117601 eq117650
  have eq117696 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq117673 eq26
    | exact resolve eq26 eq117673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq117898 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117381 eq117696
    | exact resolve eq117696 eq117381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117381 eq117696
  have eq118144 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq117898 eq27
    | exact resolve eq27 eq117898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq117898
  have eq118164 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq116678 eq118144
    | exact resolve eq118144 eq116678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116678 eq118144
  have eq118169 : False := by grind
  exact eq118169

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxx_pxy_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq74
    | exact resolve eq74 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq102
    | exact resolve eq102 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq126
    | exact resolve eq126 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq126
  have eq135 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq252 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq261 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq8261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8261
    | exact resolve eq8261 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8261
  have eq8273 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8262
       have r₂ := eq27
       grind)
    | exact resolve eq8262 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq8277 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8273
    | exact resolve eq8273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8273
  have eq8279 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8277
    | exact resolve eq8277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8277
  have eq8282 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8279 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8279
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8279
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8279
       grind)
    | exact resolve eq12 eq8279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8279
  have eq8296 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8282
       have r₂ := eq26
       grind)
    | exact resolve eq8282 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8282
  have eq8298 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8296
    | exact resolve eq8296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8299 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq8298
  have eq8321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8299 eq97
    | exact resolve eq97 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299
  have eq8329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8321
  have eq8331 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8329
       have r₂ := eq27
       grind)
    | exact resolve eq8329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq8334 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8331
       grind)
    | exact superpose eq8331 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8331
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8331
       grind)
    | exact resolve eq12 eq8331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331
  have eq8348 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8334
       have r₂ := eq18
       grind)
    | exact resolve eq8334 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334
  have eq8350 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8348
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8348
    | exact resolve eq8348 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8348
  have eq8351 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8350
  have eq8369 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq8351
       grind)
    | exact superpose eq8351 eq73
    | exact resolve eq73 eq8351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8351
  have eq8383 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8369
    | exact resolve eq8369 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8383 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8398
    | exact resolve eq8398 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8398
  have eq8412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8401
       have r₂ := eq27
       grind)
    | exact resolve eq8401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8401
  have eq8416 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8412
    | exact resolve eq8412 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8412
  have eq8418 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8416
    | exact resolve eq8416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8416
  have eq8419 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8418
  have eq8423 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8419 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8419
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8419
       grind)
    | exact resolve eq12 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8419
  have eq8437 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8423
       have r₂ := eq26
       grind)
    | exact resolve eq8423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8423
  have eq8439 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8437
    | exact resolve eq8437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8437
  have eq8440 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8439
  have eq8470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8440 eq8383
    | exact resolve eq8383 eq8440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8383 eq8440
  have eq8472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8470
  have eq8476 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8472
       have r₂ := eq27
       grind)
    | exact resolve eq8472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8626 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8476 eq27
    | exact resolve eq27 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8628 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8476 eq65
    | (have r₁ := eq65
       have r₂ := eq8476
       grind)
    | exact resolve eq65 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq8629 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8476 eq261
    | exact resolve eq261 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq8476
  have eq8639 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8628
  have eq8852 : (τ (σ y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8629 eq127
    | exact resolve eq127 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8892 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq8852
    | exact resolve eq8852 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8852
  have eq9085 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8639 eq93
    | exact resolve eq93 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq9086 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8639 eq97
    | exact resolve eq97 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq8639
  have eq9100 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq9086
  have eq9112 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq9085
    | exact resolve eq9085 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq9085
  have eq9115 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq9112
       have r₂ := eq64
       grind)
    | exact resolve eq9112 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq9112
  have eq9121 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq9115
       grind)
    | exact superpose eq9115 eq73
    | exact resolve eq73 eq9115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9137 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9121
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq9121
    | exact resolve eq9121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121
  have eq15587 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9100 eq8629
    | exact resolve eq8629 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629 eq9100
  have eq15655 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq15587
  have eq15663 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15655
       have r₂ := eq8626
       grind)
    | exact resolve eq15655 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8626 eq15655
  have eq15678 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15663
       grind)
    | exact superpose eq15663 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15663
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15663
       grind)
    | exact resolve eq12 eq15663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15663
  have eq15702 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15678
       have r₂ := eq18
       grind)
    | exact resolve eq15678 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15678
  have eq15704 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15702
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15702
    | exact resolve eq15702 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15702
  have eq15705 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq15704
  have eq15707 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15705
       have i₂ := eq9115
       grind)
    | exact superpose eq9115 eq15705
    | exact resolve eq15705 eq9115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9115 eq15705
  have eq15887 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8892
       have i₂ := eq15707
       grind)
    | exact superpose eq15707 eq8892
    | exact resolve eq8892 eq15707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8892 eq15707
  have eq15956 : y = (M.op x y) := by grind
  clear eq15887
  have eq16131 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15956 eq20
    | exact resolve eq20 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16145 : (σ (k y x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq15956 eq135
    | exact resolve eq135 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq16178 : y = (M.op y y) := by
    first
    | exact superpose eq15956 eq252
    | exact resolve eq252 eq15956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq15956
  have eq16233 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq16145
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16145
    | exact resolve eq16145 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq16145
  have eq16245 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16131
    | exact resolve eq16131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16131
  have eq16263 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq9137 eq16233
    | exact resolve eq16233 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9137 eq16233
  have eq16271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16245 eq26
    | exact resolve eq26 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq16468 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq16178
       grind)
    | exact superpose eq16178 eq117
    | exact resolve eq117 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq16178
  have eq16552 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16245 eq16468
    | exact resolve eq16468 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16468
  have eq16574 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16552
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16552
    | exact resolve eq16552 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16552
  have eq16592 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16245 eq16574
    | exact resolve eq16574 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16574
  have eq16688 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq16592 eq14
    | exact resolve eq14 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16762 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16245 eq16263
    | exact resolve eq16263 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245 eq16263
  have eq16763 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq16592 eq16762
    | exact resolve eq16762 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592 eq16762
  have eq16774 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16763 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq16763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16763
  have eq16775 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq16774
  have eq16777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16271 eq16775
    | exact resolve eq16775 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775
  have eq16788 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq16777
       have r₂ := eq27
       grind)
    | exact resolve eq16777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16777
  have eq16799 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq16271 eq16788
    | exact resolve eq16788 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16788
  have eq16825 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq16799 eq14
    | exact resolve eq14 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17221 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq16271 eq16688
    | exact resolve eq16688 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16688
  have eq17346 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17221 eq16825
    | exact resolve eq16825 eq17221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16825
  have eq17402 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16271 eq17346
    | exact resolve eq17346 eq16271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16271 eq17346
  have eq17451 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq17402 eq17221
    | exact resolve eq17221 eq17402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17221
  have eq17452 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16799 eq17451
    | exact resolve eq17451 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17451
  have eq17463 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq17402 eq17452
    | exact resolve eq17452 eq17402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17402 eq17452
  have eq17467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16799 eq17463
    | exact resolve eq17463 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16799 eq17463
  have eq17469 : False := by grind
  exact eq17469
