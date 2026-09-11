import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq79 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq67 (M.op X0 X0)
       grind)
    | exact superpose eq67 eq131
    | exact resolve eq131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq349 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 (τ X0) X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq367 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq349 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq349
    | (have j0 := eq349 X0 X1
       grind)
    | exact resolve eq349 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq349
  have eq373 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq367 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq367 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq377 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq580 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq377
    | (have j0 := eq377 X1 (τ X0)
       grind)
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq377 (σ X1) X0
       grind)
    | exact superpose eq377 eq15
    | (have j1 := eq377 (σ X1) X0
       grind)
    | exact resolve eq15 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq608 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq613 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq580
    | (have j0 := eq580 X0 X1
       grind)
    | exact resolve eq580 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq580
  have eq639 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq613 (τ X0) X1
       grind)
    | exact superpose eq613 eq17
    | (have j1 := eq613 X1 (τ X0)
       grind)
    | exact resolve eq17 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq613
  have eq646 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq639
  have eq2291 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq646 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq646
    | (have j0 := eq646 (σ X0) X1
       grind)
    | exact resolve eq646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq2376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2291 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2291
    | (have j0 := eq2291 X0 X1
       grind)
    | exact resolve eq2291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2383 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2376 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq2376
    | (have j0 := eq2376 X0 X1
       grind)
    | exact resolve eq2376 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq2386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2383 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2383
    | (have j0 := eq2383 X0 X1
       grind)
    | exact resolve eq2383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2986 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq608 x y
       grind)
    | exact superpose eq608 eq16
    | (have j1 := eq608 x y
       grind)
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq3138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2986
       have i₂ := eq2386 x y
       grind)
    | exact superpose eq2386 eq2986
    | (have j1 := eq2386 x y
       grind)
    | (have r₁ := eq2986
       have r₂ := eq2386 x y
       grind)
    | exact resolve eq2986 eq2386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386 eq2986
  have eq3139 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3138
  have eq3150 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq208 y x
       have i₂ := eq3139
       grind)
    | exact superpose eq3139 eq208
    | exact resolve eq208 eq3139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3162 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3139
       grind)
    | exact superpose eq3139 eq21
    | exact resolve eq21 eq3139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3139
  have eq3167 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3162 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3162
    | exact resolve eq3162 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3178 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3150 X0
       have i₂ := eq208 x X0
       grind)
    | exact superpose eq208 eq3150
    | exact resolve eq3150 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq3150
  have eq3287 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3167 X0
       grind)
    | exact superpose eq3167 eq10
    | (have j1 := eq3167 X0
       grind)
    | exact resolve eq10 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3334 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3287 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3287
    | (have j0 := eq3287 X0
       grind)
    | exact resolve eq3287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq3361 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3334 X2
       grind)
    | exact superpose eq3334 eq21
    | (have j1 := eq3334 X2
       grind)
    | exact resolve eq21 eq3334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3367 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq3361 X0 x X2
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3361
    | (have j0 := eq3361 X0 x X0
       grind)
    | exact resolve eq3361 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3361
  have eq3538 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3367 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3539 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq6546 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq3178 X1
       grind)
    | exact superpose eq3178 eq79
    | (have j1 := eq3178 X1
       grind)
    | exact resolve eq79 eq3178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq6615 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq6546 X0 X1
       have i₂ := eq79 x X0
       grind)
    | exact superpose eq79 eq6546
    | (have j0 := eq6546 X0 X0
       grind)
    | exact resolve eq6546 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq6546
  have eq7245 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq6615 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6615
  have eq7246 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq7245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7245
  have eq7289 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7246 (σ x)
       grind)
    | exact superpose eq7246 eq16
    | exact resolve eq16 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246
  have eq7325 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7289
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7289
    | exact resolve eq7289 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7289
  have eq7351 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7325
       have i₂ := eq3539 x
       grind)
    | exact superpose eq3539 eq7325
    | exact resolve eq7325 eq3539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq7325
  have eq7352 : False := by grind
  exact eq7352

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq79 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq21
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq67 (M.op X0 X0)
       grind)
    | exact superpose eq67 eq131
    | exact resolve eq131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq352 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 (τ X0) X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq370 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq352
  have eq376 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq370 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq370 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq380 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq376
    | (have j0 := eq376 X0 X1
       grind)
    | exact resolve eq376 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq583 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq380
    | (have j0 := eq380 X1 (τ X0)
       grind)
    | exact resolve eq380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq380 (σ X1) X0
       grind)
    | exact superpose eq380 eq15
    | (have j1 := eq380 (σ X1) X0
       grind)
    | exact resolve eq15 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq611 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq616 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq583
    | (have j0 := eq583 X0 X1
       grind)
    | exact resolve eq583 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq583
  have eq642 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq616 (τ X0) X1
       grind)
    | exact superpose eq616 eq17
    | (have j1 := eq616 X1 (τ X0)
       grind)
    | exact resolve eq17 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq616
  have eq649 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq642
    | (have j0 := eq642 X0 X1
       grind)
    | exact resolve eq642 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq642
  have eq2302 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq649 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq649
    | (have j0 := eq649 (σ X0) X1
       grind)
    | exact resolve eq649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq2387 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2302 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2302
    | (have j0 := eq2302 X0 X1
       grind)
    | exact resolve eq2302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq2394 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2387 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq2387
    | (have j0 := eq2387 X0 X1
       grind)
    | exact resolve eq2387 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2397 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2394 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2394
    | (have j0 := eq2394 X0 X1
       grind)
    | exact resolve eq2394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2985 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq611 x y
       grind)
    | exact superpose eq611 eq16
    | (have j1 := eq611 x y
       grind)
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq3137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2985
       have i₂ := eq2397 x y
       grind)
    | exact superpose eq2397 eq2985
    | (have j1 := eq2397 x y
       grind)
    | (have r₁ := eq2985
       have r₂ := eq2397 x y
       grind)
    | exact resolve eq2985 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq2985
  have eq3138 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq3137
  have eq3149 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq209 y x
       have i₂ := eq3138
       grind)
    | exact superpose eq3138 eq209
    | exact resolve eq209 eq3138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3161 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3138
       grind)
    | exact superpose eq3138 eq21
    | exact resolve eq21 eq3138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3166 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3161 X0 x
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3161
    | exact resolve eq3161 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq3177 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3149 X0
       have i₂ := eq209 x X0
       grind)
    | exact superpose eq209 eq3149
    | exact resolve eq3149 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3149
  have eq3290 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3166 X0
       grind)
    | exact superpose eq3166 eq10
    | (have j1 := eq3166 X0
       grind)
    | exact resolve eq10 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166
  have eq3337 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq3290 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3290
    | (have j0 := eq3290 X0
       grind)
    | exact resolve eq3290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3364 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 y X0 y
       have i₂ := eq3337 X2
       grind)
    | exact superpose eq3337 eq21
    | (have j1 := eq3337 X2
       grind)
    | exact resolve eq21 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3370 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq3364 X0 x X2
       have i₂ := eq21 x x X0 x
       grind)
    | exact superpose eq21 eq3364
    | (have j0 := eq3364 X0 x X0
       grind)
    | exact resolve eq3364 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3364
  have eq3540 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3370 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq3541 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3540
  have eq6518 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X0)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq3177 X1
       grind)
    | exact superpose eq3177 eq79
    | (have j1 := eq3177 X1
       grind)
    | exact resolve eq79 eq3177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq6587 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq6518 X0 X1
       have i₂ := eq79 x X0
       grind)
    | exact superpose eq79 eq6518
    | (have j0 := eq6518 X0 X0
       grind)
    | exact resolve eq6518 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq6518
  have eq7218 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq6587 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq7219 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq7218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7261 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7219 (σ x)
       grind)
    | exact superpose eq7219 eq16
    | exact resolve eq16 eq7219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7219
  have eq7297 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7261
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7261
    | exact resolve eq7261 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7261
  have eq7322 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7297
       have i₂ := eq3541 x
       grind)
    | exact superpose eq3541 eq7297
    | exact resolve eq7297 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541 eq7297
  have eq7323 : False := by grind
  exact eq7323

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq360 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq369 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq369 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq369 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq369 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq378 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq360 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq360 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq376
    | (have j0 := eq376 X0 X1
       grind)
    | exact resolve eq376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq392 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq378
    | (have j0 := eq378 X0 X1
       grind)
    | exact resolve eq378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq393 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq398 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       have j1 := eq391 X0 X1
       grind)
    | (have r₁ := eq393 X0 X1
       have r₂ := eq391 X0 X1
       grind)
    | exact resolve eq393 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq393
  have eq399 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq398 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq398
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq398 x y
       grind)
    | exact superpose eq398 eq16
    | exact resolve eq16 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq501 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq399 X0 (τ X1)
       grind)
    | exact superpose eq399 eq18
    | exact resolve eq18 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq399
  have eq522 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq501
    | exact resolve eq501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq532 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq522
    | exact resolve eq522 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq559 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq410
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq410
    | exact resolve eq410 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq532
  have eq560 : False := by grind
  exact eq560

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq281 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq291 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq289 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq394 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 (M.op (M.op X2 X1) X3)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq291 X2 (M.op (M.op X3 X1) X0)
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq291
    | (have j0 := eq291 X0 X1
       grind)
    | exact resolve eq291 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq291 X0 X1
       grind)
    | exact superpose eq291 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq291 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq13 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq291 (σ x) (σ y)
       grind)
    | exact superpose eq291 eq16
    | (have j1 := eq291 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq411 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq414 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq410 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq410 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq410 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq428 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq414 X0 (τ X1)
       grind)
    | exact superpose eq414 eq18
    | (have j1 := eq414 X0 (τ X1)
       grind)
    | exact resolve eq18 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq445 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq445 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq445
    | (have j0 := eq445 X0 X1
       grind)
    | exact resolve eq445 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq453 X0 X1 X2 X3
       have i₂ := eq291 X0 X1
       grind)
    | exact superpose eq291 eq453
    | (have j0 := eq453 X0 X1 X2 X3
       have j1 := eq291 X0 X1
       grind)
    | (have r₁ := eq453 X0 X1 X2 X3
       have r₂ := eq291 X0 X1
       grind)
    | exact resolve eq453 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq597 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq1126 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq428 (τ X0) X1
       grind)
    | exact superpose eq428 eq17
    | (have j1 := eq428 (τ X0) X1
       grind)
    | exact resolve eq17 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq428
  have eq1133 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1126
    | (have j0 := eq1126 X0 X1
       grind)
    | exact resolve eq1126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1146 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1133 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1133
    | (have j0 := eq1133 X0 X1
       grind)
    | exact resolve eq1133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1149 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1213 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1149 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1149
    | (have j0 := eq1149 X1 (σ X0)
       grind)
    | exact resolve eq1149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1593 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X0
       have i₂ := eq414 X0 (σ X0)
       grind)
    | exact superpose eq414 eq1213
    | (have j0 := eq1213 X1 X0
       have j1 := eq414 X0 (σ X1)
       grind)
    | exact resolve eq1213 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq1213
  have eq1638 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1593 X0 X1
       have j1 := eq445 X0 (σ X1)
       grind)
    | (have r₁ := eq1593 X0 X1
       have r₂ := eq445 X0 (σ X1)
       grind)
    | exact resolve eq1593 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq1593
  have eq1806 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1638 (σ X0) X1
       grind)
    | exact superpose eq1638 eq28
    | (have j1 := eq1638 (σ X0) X1
       grind)
    | exact resolve eq28 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1638
  have eq1820 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1806 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1806
    | (have j0 := eq1806 X0 X1
       grind)
    | exact resolve eq1806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806
  have eq1836 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1820
    | (have j0 := eq1820 X0 X1
       grind)
    | exact resolve eq1820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1845 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1836 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1836
    | (have j0 := eq1836 X0 X1
       grind)
    | exact resolve eq1836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1845 x y
       grind)
    | exact superpose eq1845 eq16
    | (have j1 := eq1845 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1845 x y
       grind)
    | exact resolve eq16 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1956 : x = (k x y) := by grind
  clear eq1931
  have eq1985 : ∀ X0 X1 : G, x = (M.op x y) ∨ x = (k x (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 x y X0 X1
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq601
    | (have j0 := eq601 x y X0 X1
       grind)
    | exact resolve eq601 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq1988 : ∀ X0 X1 : G, x = (k x (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1985 X0 X1
       have j1 := eq453 x y X0 X1
       grind)
    | (have r₁ := eq1985 X0 X1
       have r₂ := eq453 x y x x
       grind)
    | exact resolve eq1985 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq1985
  have eq2010 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq394 x y x x
       have i₂ := eq1988 x x
       grind)
    | exact superpose eq1988 eq394
    | (have j0 := eq394 x y x x
       grind)
    | exact resolve eq394 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq2016 : x = (M.op x y) := by grind
  clear eq2010
  have eq2030 : ∀ X0 : G, x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1988 x X0
       have i₂ := eq2016
       grind)
    | exact superpose eq2016 eq1988
    | exact resolve eq1988 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2035 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq2016
       grind)
    | exact superpose eq2016 eq63
    | exact resolve eq63 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2044 : x = (k x x) := by
    first
    | (have i₁ := eq2030 y
       have i₂ := eq2016
       grind)
    | exact superpose eq2016 eq2030
    | exact resolve eq2030 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2077 : x = (M.op x x) := by
    first
    | (have i₁ := eq2044
       have i₂ := eq292 x
       grind)
    | exact superpose eq292 eq2044
    | exact resolve eq2044 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq2044
  have eq2105 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2035 X0 x
       have i₂ := eq2077
       grind)
    | exact superpose eq2077 eq2035
    | exact resolve eq2035 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq8407 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq411
       have i₂ := eq2016
       grind)
    | exact superpose eq2016 eq411
    | exact resolve eq411 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq2016
  have eq8414 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq8407
  have eq8422 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8414
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq8414
    | exact resolve eq8414 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq8414
  have eq8428 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8422
       grind)
    | exact superpose eq8422 eq16
    | exact resolve eq16 eq8422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8471 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8428
       have i₂ := eq2105 x
       grind)
    | exact superpose eq2105 eq8428
    | exact resolve eq8428 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq8428
  have eq8476 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq8471
       have i₂ := eq2077
       grind)
    | exact superpose eq2077 eq8471
    | exact resolve eq8471 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077 eq8471
  have eq8477 : False := by grind
  exact eq8477

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
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
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X0) ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) X0) X0
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op (M.op x y) X0) X0) = (k (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 (M.op (M.op x y) X0) X0
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq186
    | exact resolve eq186 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq192 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (k (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq176 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) X0) X0
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq607 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq28 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X2)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq620 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq623 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq41
    | exact resolve eq41 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq638 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq637
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq637
    | exact resolve eq637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq640 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq638
    | exact resolve eq638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq623 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq623
    | (have j0 := eq623 (σ X0)
       grind)
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq640 eq620
    | exact resolve eq620 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq640
  have eq657 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq650
       have r₂ := eq27
       grind)
    | exact resolve eq650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq662 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq657 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq657 eq13
    | exact resolve eq13 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq666 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq662
       have r₂ := eq664
       grind)
    | exact resolve eq662 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq664
  have eq668 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq666 eq116
    | exact resolve eq116 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq666
  have eq675 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq668
    | exact resolve eq668 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq680 : x ≠ y ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq623 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq623
    | (have j0 := eq623 y
       grind)
    | exact resolve eq623 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq608 y y X0
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq608
    | (have j0 := eq608 y y x
       grind)
    | exact resolve eq608 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq28 eq694
    | (have j0 := eq694 X0
       have j1 := eq28 y y
       grind)
    | exact resolve eq694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq722 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ x = y ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq675 eq721
    | (have j0 := eq721 X0
       grind)
    | exact resolve eq721 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq797 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq722 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq722
    | (have j0 := eq722 y
       grind)
    | exact resolve eq722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 y) X1)) = (M.op X1 (M.op x X0)) ∨ x = y ∨ x = (k y y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op x X0) X0
       have i₂ := eq722 X0
       grind)
    | exact superpose eq722 eq16
    | exact resolve eq16 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq825 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op x X0)) ∨ x = y ∨ x = (k y y) := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq814
    | exact resolve eq814 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq830 : x = (k y y) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq675 eq797
    | exact resolve eq797 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq834 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq608 y y X0
       have i₂ := eq830
       grind)
    | exact superpose eq830 eq608
    | (have j0 := eq608 y y x
       grind)
    | exact resolve eq608 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1052 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq825 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq825
    | (have j0 := eq825 y X0
       grind)
    | exact resolve eq825 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1096 : ∀ X0 : G, (k X0 y) = (M.op X0 (M.op x y)) ∨ (M.op y y) = X0 ∨ x = y ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq1052 X0
       grind)
    | exact superpose eq1052 eq28
    | (have j0 := eq28 X0 y
       grind)
    | exact resolve eq28 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1179 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq607 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq607
    | (have j0 := eq607 (σ X0) (σ X1)
       grind)
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1179 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1179
    | (have j0 := eq1179 X0 X1
       grind)
    | exact resolve eq1179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq4622 : (M.op y y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq834 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq834
    | (have j0 := eq834 y
       grind)
    | exact resolve eq834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq4777 : (k y y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq28 eq4622
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq4622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4622
  have eq4802 : x = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq830 eq4777
    | exact resolve eq4777 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq4803 : y = (M.op y y) ∨ x = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq4802
  have eq4812 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq4803
       grind)
    | exact superpose eq4803 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq4803
       grind)
    | exact resolve eq13 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4819 : y = (k y y) ∨ x = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq4812
  have eq4822 : x = y ∨ x = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq830 eq4819
    | exact resolve eq4819 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq4819
  have eq4823 : x = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq4822
  have eq4827 : x = (k y y) ∨ y = (M.op y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq4823 eq1096
    | (have j0 := eq1096 y
       grind)
    | exact resolve eq1096 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq4830 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4823 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4833 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq4823 eq179
    | exact resolve eq179 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4836 : x = (k y y) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq4827
  have eq4839 : x = (k y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq675 eq4836
    | exact resolve eq4836 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836
  have eq4840 : x = (k y y) ∨ x = y := by grind
  clear eq4839
  have eq4844 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq4840
       grind)
    | exact superpose eq4840 eq41
    | exact resolve eq41 eq4840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4848 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq608 y y X0
       have i₂ := eq4840
       grind)
    | exact superpose eq4840 eq608
    | (have j0 := eq608 y y x
       grind)
    | exact resolve eq608 eq4840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4849 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4833 eq4848
    | exact resolve eq4848 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq4850 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4844
    | exact resolve eq4844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq4852 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4850
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4850
    | exact resolve eq4850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850
  have eq4859 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4852 eq623
    | (have j0 := eq623 (σ y)
       grind)
    | exact resolve eq623 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq4860 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4852 eq607
    | (have j0 := eq607 (σ x) (σ y)
       grind)
    | exact resolve eq607 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4861 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4852 eq608
    | (have j0 := eq608 (σ y) (σ y) x
       grind)
    | exact resolve eq608 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4927 : ∀ X0 X1 : G, (M.op x X1) ≠ (M.op X0 (M.op x y)) ∨ (M.op (M.op x X1) X0) = (k (M.op x X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x X1) X0
       have i₂ := eq4833 X0 X1
       grind)
    | (have i₁ := eq13 (M.op x y) X0
       have i₂ := eq4833 X0 X1
       grind)
    | exact superpose eq4833 eq13
    | (have j0 := eq13 (M.op x X1) X0
       grind)
    | (have r₁ := eq13 (M.op x (M.op x y)) x
       have r₂ := eq4833 x (M.op x y)
       grind)
    | exact resolve eq13 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4929 : ∀ X0 X1 : G, (M.op (M.op x X1) (M.op x X1)) = X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op x X1)
       have i₂ := eq4833 X0 X1
       grind)
    | (have i₁ := eq28 X0 (M.op x y)
       have i₂ := eq4833 X0 X1
       grind)
    | exact superpose eq4833 eq28
    | (have j0 := eq28 X0 (M.op x X1)
       grind)
    | exact resolve eq28 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5064 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4830 eq690
    | exact resolve eq690 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5131 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq4849 x
       grind)
    | exact superpose eq4849 eq18
    | (have j1 := eq4849 x
       grind)
    | exact resolve eq18 eq4849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5790 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq4861
    | (have j0 := eq4861 (σ y)
       grind)
    | exact resolve eq4861 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5942 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq5790
    | (have j1 := eq28 (σ y) (σ y)
       grind)
    | exact resolve eq5790 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5790
  have eq5945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq4852 eq5942
    | exact resolve eq5942 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5942
  have eq5958 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq5945 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq5945
       grind)
    | exact resolve eq13 eq5945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq5965 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq5958
  have eq5966 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4852 eq5965
    | exact resolve eq5965 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq5985 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq5966 eq179
    | exact resolve eq179 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6057 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5985 eq4861
    | exact resolve eq4861 eq5985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861 eq5985
  have eq6124 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq6057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6150 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq6124 X0
       grind)
    | (have r₁ := eq6124 X0
       have r₂ := eq4859
       grind)
    | exact resolve eq6124 eq4859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859 eq6124
  have eq6202 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6150 eq5966
    | exact resolve eq5966 eq6150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966 eq6150
  have eq6214 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6202
  have eq6227 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq6214
       have r₂ := eq4860
       grind)
    | exact resolve eq6214 eq4860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860 eq6214
  have eq6244 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6227 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq6227
       grind)
    | exact resolve eq13 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6251 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq6227
  have eq6252 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq6244
  have eq6253 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4852 eq6252
    | exact resolve eq6252 eq4852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852 eq6252
  have eq6254 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq6253
       have r₂ := eq6251
       grind)
    | exact resolve eq6253 eq6251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6251 eq6253
  have eq6271 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq6254 eq179
    | exact resolve eq179 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6279 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq6271
    | (have j0 := eq6271 X0 (σ y)
       grind)
    | exact resolve eq6271 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6345 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq6271 eq690
    | exact resolve eq690 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6440 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq6345
    | exact resolve eq6345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq6445 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq6440
    | exact resolve eq6440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440
  have eq6454 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6279 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq6279 (σ x)
       grind)
    | exact resolve eq13 eq6279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6712 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq6254 eq6454
    | (have j0 := eq6454 (σ y)
       grind)
    | exact resolve eq6454 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6454
  have eq6719 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by grind
  clear eq6712
  have eq9887 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq5064 eq4849
    | exact resolve eq4849 eq5064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9897 : y ≠ (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) ∨ x = y := by grind
  clear eq5064
  have eq9899 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by grind
  clear eq9887
  have eq9904 : y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq4830 eq9899
    | exact resolve eq9899 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830 eq9899
  have eq9907 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | (have r₁ := eq9904
       have r₂ := eq9897
       grind)
    | exact resolve eq9904 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897 eq9904
  have eq9915 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = y ∨ y = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq9907 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq9907
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq9907
       grind)
    | exact resolve eq13 eq9907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9907
  have eq9923 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = y ∨ y = (M.op y y) ∨ x = (k y (M.op x y)) := by grind
  clear eq9915
  have eq9935 : x = (k y (M.op x y)) ∨ x = y ∨ y = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq4823 eq9923
    | exact resolve eq9923 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823 eq9923
  have eq9936 : y = (M.op y y) ∨ x = y ∨ x = (k y (M.op x y)) := by grind
  clear eq9935
  have eq9946 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq9936
       grind)
    | exact superpose eq9936 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq9936
       grind)
    | exact resolve eq13 eq9936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936
  have eq9953 : y = (k y y) ∨ x = y ∨ x = (k y (M.op x y)) := by grind
  clear eq9946
  have eq9962 : x = y ∨ x = y ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq4840 eq9953
    | exact resolve eq9953 eq4840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9953
  have eq9963 : x = (k y (M.op x y)) ∨ x = y := by grind
  clear eq9962
  have eq9965 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq9963 eq42
    | exact resolve eq42 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9968 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq9965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9965
    | exact resolve eq9965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq9970 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq9968
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9968
    | exact resolve eq9968 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9968
  have eq9976 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9970 eq608
    | (have j0 := eq608 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq608 eq9970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq9970
  have eq9977 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6271 eq9976
    | exact resolve eq9976 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6271 eq9976
  have eq10092 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9977 eq28
    | (have j0 := eq28 X0 (σ (M.op x y))
       grind)
    | exact resolve eq28 eq9977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9977
  have eq11039 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq10092 eq26
    | (have j1 := eq10092 (σ x)
       grind)
    | exact resolve eq26 eq10092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10092
  have eq11719 : (k (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) x) ∨ x = y := by
    first
    | (have j0 := eq4927 x (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927
  have eq11789 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (M.op x (M.op x y)) x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11719 eq179
    | exact resolve eq179 eq11719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11719
  have eq13539 : ∀ X0 X1 : G, (M.op (M.op x X1) X1) ≠ X0 ∨ (M.op X0 (M.op x X1)) = (k X0 (M.op x X1)) ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op x X1) X1 x
       have i₂ := eq4929 X0 X1
       grind)
    | (have i₁ := eq182 X0 X1 x
       have i₂ := eq4929 (M.op (M.op x X1) X0) X1
       grind)
    | exact superpose eq4929 eq182
    | (have j1 := eq4929 X0 X1
       grind)
    | (have r₁ := eq182 (M.op x X1) (M.op x X1) x
       have r₂ := eq4929 (M.op (M.op x (M.op x X1)) (M.op x X1)) X1
       grind)
    | (have r₁ := eq182 (M.op x X1) X1 x
       have r₂ := eq4929 (M.op (M.op x X1) X1) X1
       grind)
    | exact resolve eq182 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq13543 : ∀ X0 X1 : G, (M.op (M.op x X1) (M.op x y)) = X0 ∨ x = y ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4833 (M.op x X1) X1
       have i₂ := eq4929 X0 X1
       grind)
    | (have i₁ := eq4833 X0 X1
       have i₂ := eq4929 (M.op X0 (M.op x X1)) X1
       grind)
    | exact superpose eq4929 eq4833
    | (have j1 := eq4929 X0 X1
       grind)
    | exact resolve eq4833 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq13556 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y ∨ (M.op (M.op x X1) (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13543 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq13619 : ∀ X0 X1 : G, (M.op (M.op x X1) X1) ≠ X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq4833 eq13539
    | (have j0 := eq13539 X0 X1
       grind)
    | (have r₁ := eq13539 (M.op (M.op x (M.op x X1)) (M.op x y)) (M.op x X1)
       have r₂ := eq4833 (M.op x (M.op x X1)) X1
       grind)
    | (have r₁ := eq13539 (M.op (M.op x (M.op x y)) (M.op x X1)) (M.op x y)
       have r₂ := eq4833 (M.op x (M.op x y)) X1
       grind)
    | exact resolve eq13539 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4833 eq13539
  have eq13620 : ∀ X0 X1 : G, (M.op (M.op x X1) X1) ≠ X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq13619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13619
  have eq15710 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13620 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13620
    | (have j0 := eq13620 X0 y
       grind)
    | exact resolve eq13620 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15712 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5131 eq13620
    | (have j0 := eq13620 X0 y
       grind)
    | exact resolve eq13620 eq5131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15847 : ∀ X0 : G, (M.op (M.op x (k (M.op x (M.op x y)) x)) (M.op x y)) ≠ X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x (k (M.op x (M.op x y)) x))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq11789 eq13620
    | (have j0 := eq13620 X0 (k (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq13620 (M.op (M.op x (M.op x y)) (k (M.op x (M.op x y)) x)) (M.op x y)
       have r₂ := eq11789 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13620 (M.op (M.op x (k (M.op x (M.op x y)) x)) (M.op x y)) (k (M.op x (M.op x y)) x)
       have r₂ := eq11789 (M.op x (k (M.op x (M.op x y)) x))
       grind)
    | exact resolve eq13620 eq11789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13620
  have eq15908 : ∀ X0 : G, (M.op (M.op x (k (M.op x (M.op x y)) x)) (M.op x y)) ≠ X0 ∨ (M.op X0 (M.op x y)) = (k X0 (M.op x (k (M.op x (M.op x y)) x))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15847
  have eq15981 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq16016 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x (k (M.op x (M.op x y)) x))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15908 X0
       have j1 := eq13556 X0 (k (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq15908 (k (M.op x (k (M.op x (M.op x y)) x)) (M.op x x))
       have r₂ := eq13556 (M.op x (k (M.op x (M.op x y)) x)) x
       grind)
    | (have r₁ := eq15908 X0
       have r₂ := eq13556 X0 (k (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq15908 (M.op (M.op x x) (M.op x y))
       have r₂ := eq13556 (M.op (M.op x (k (M.op x (M.op x y)) x)) (M.op x y)) x
       grind)
    | exact resolve eq15908 eq13556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556 eq15908
  have eq16071 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15981 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq15981 (k (M.op x y) (M.op x y))
       have r₂ := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq15981 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq15981 (M.op x x)
       have r₂ := eq28 (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact resolve eq15981 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15981
  have eq16099 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k X0 (M.op x (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11789 eq16016
    | exact resolve eq16016 eq11789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11789 eq16016
  have eq16178 : (σ (M.op x (M.op x y))) = (k (σ x) (σ (M.op x (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq16099 eq36
    | exact resolve eq36 eq16099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq16099
  have eq16318 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5131 eq16178
    | exact resolve eq16178 eq5131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5131
  have eq16347 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq16318
  have eq16359 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq16347
    | exact resolve eq16347 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16347
  have eq16371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16359 eq11039
    | exact resolve eq11039 eq16359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11039
  have eq16378 : (τ (σ (M.op x y))) = (k x (τ (σ (M.op x y)))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16359 eq91
    | exact resolve eq91 eq16359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16359
  have eq16387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq16371
  have eq16390 : (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq16378
    | exact resolve eq16378 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16378
  have eq16395 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16387
       have r₂ := eq27
       grind)
    | exact resolve eq16387 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16387
  have eq16858 : ∀ X0 X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op (k X0 (M.op x y)) X2)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq16071 eq179
    | exact resolve eq179 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16865 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq16071 eq179
    | exact resolve eq179 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16866 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (k (M.op X0 X1) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq16071 eq16
    | exact resolve eq16 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16927 : (M.op (M.op x y) y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16071 eq175
    | exact resolve eq175 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17035 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq4849 eq16927
    | exact resolve eq16927 eq4849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849 eq16927
  have eq17072 : ∀ X0 X1 X2 : G, (k X1 (M.op x y)) = (M.op X1 (M.op (k X0 (M.op x y)) X2)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq16071 eq16858
    | exact resolve eq16858 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq17082 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16071 eq17035
    | exact resolve eq17035 eq16071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16071 eq17035
  have eq20708 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16395 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq16395
       grind)
    | exact resolve eq13 eq16395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20710 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq16395 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq16395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16395
  have eq20723 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq20708
       have r₂ := eq20710
       grind)
    | exact resolve eq20708 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20708 eq20710
  have eq20742 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20723 eq134
    | exact resolve eq134 eq20723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20723
  have eq20759 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq20742
    | exact resolve eq20742 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq20742
  have eq20814 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20759 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq20759
       grind)
    | exact resolve eq13 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20816 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20759 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20831 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq20814
       have r₂ := eq20816
       grind)
    | exact resolve eq20814 eq20816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20814 eq20816
  have eq20926 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20831 eq134
    | exact resolve eq134 eq20831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq20831
  have eq20945 : y = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq20926
    | exact resolve eq20926 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20926
  have eq23370 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op X0 (M.op (M.op x y) X1)) ∨ x = y ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq16390 eq17072
    | exact resolve eq17072 eq16390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16390 eq17072
  have eq23696 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (M.op X0 (M.op (M.op x y) X1)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq23370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23370
  have eq23748 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq188 eq23696
    | exact resolve eq23696 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23696
  have eq23883 : (M.op y y) = (M.op y (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq23748 sF0
       grind)
    | exact superpose eq23748 eq175
    | exact resolve eq175 eq23748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq23748
  have eq23983 : (k y y) = (M.op y (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq28 eq23883
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq23883 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23883
  have eq24024 : x = (M.op y (k (M.op x y) (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq4840 eq23983
    | exact resolve eq23983 eq4840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23983
  have eq24059 : x = (M.op y y) ∨ x = y ∨ y = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20945 eq24024
    | exact resolve eq24024 eq20945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24089 : x = (M.op y y) ∨ x = y ∨ y = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq24059
  have eq24102 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq24089
       have r₂ := eq680
       grind)
    | exact resolve eq24089 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24089
  have eq24128 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq24102
       grind)
    | exact superpose eq24102 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq24102
       grind)
    | exact resolve eq13 eq24102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24135 : x ≠ y ∨ x = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq24102
  have eq24136 : y = (k y y) ∨ x = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq24128
  have eq24138 : x = y ∨ x = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq675 eq24136
    | exact resolve eq24136 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24136
  have eq24142 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24138
       have r₂ := eq24135
       grind)
    | exact resolve eq24138 eq24135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24135 eq24138
  have eq24155 : x = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24142 eq17082
    | exact resolve eq17082 eq24142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082
  have eq24157 : x = (M.op y x) ∨ x = y ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24142 eq24024
    | exact resolve eq24024 eq24142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24142
  have eq24177 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24157
       have r₂ := eq680
       grind)
    | exact resolve eq24157 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq24179 : y = (M.op y y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24155
       have r₂ := eq680
       grind)
    | exact resolve eq24155 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq24155
  have eq24266 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq24177
       grind)
    | exact superpose eq24177 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq24177
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq24177
       grind)
    | exact resolve eq13 eq24177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24273 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq24177
  have eq24274 : y = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq24266
  have eq24276 : x = y ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq675 eq24274
    | exact resolve eq24274 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24274
  have eq24280 : x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq24276
       have r₂ := eq24273
       grind)
    | exact resolve eq24276 eq24273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24273 eq24276
  have eq24313 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq690 y
       have i₂ := eq24280
       grind)
    | exact superpose eq24280 eq690
    | exact resolve eq690 eq24280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq24327 : (k x y) = (M.op y x) ∨ x = (M.op y x) := by grind
  clear eq24313
  have eq24426 : x ≠ (k x y) ∨ x = (M.op y x) := by grind
  have eq26372 : y ≠ y ∨ y = (k y y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq24179
       grind)
    | exact superpose eq24179 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq24179
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq24179
       grind)
    | exact resolve eq13 eq24179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26380 : x ≠ y ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by grind
  clear eq24179
  have eq26381 : y = (k y y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by grind
  clear eq26372
  have eq26383 : x = y ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq675 eq26381
    | exact resolve eq26381 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq26381
  have eq26386 : x = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26383
       have r₂ := eq26380
       grind)
    | exact resolve eq26383 eq26380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26380 eq26383
  have eq26405 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq26386 eq188
    | exact resolve eq188 eq26386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26386
  have eq26660 : x ≠ (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26405
  have eq26683 : x = (M.op y y) := by
    first
    | (have r₁ := eq26660
       have r₂ := eq24280
       grind)
    | exact resolve eq26660 eq24280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24280 eq26660
  have eq26736 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq26683
       grind)
    | exact superpose eq26683 eq13
    | exact resolve eq13 eq26683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26741 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 y X0 y
       have i₂ := eq26683
       grind)
    | exact superpose eq26683 eq179
    | exact resolve eq179 eq26683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26756 : x = (k y y) := by
    first
    | (have r₁ := eq26736
       have r₂ := eq4840
       grind)
    | exact resolve eq26736 eq4840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840 eq26736
  have eq26762 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq647 y
       have i₂ := eq26756
       grind)
    | exact superpose eq26756 eq647
    | (have j0 := eq647 y
       grind)
    | exact resolve eq647 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq26769 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26762
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26762
    | exact resolve eq26762 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26762
  have eq26772 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26769
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26769
    | exact resolve eq26769 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26769
  have eq26775 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26772
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26772
    | exact resolve eq26772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26772
  have eq26800 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq26741 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26741
    | (have j0 := eq26741 X0 y
       grind)
    | exact resolve eq26741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26741
  have eq27072 : ∀ X0 : G, y ≠ (M.op X0 (M.op x y)) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq26800 X0
       grind)
    | exact superpose eq26800 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq26800 x
       grind)
    | exact resolve eq13 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27074 : ∀ X0 : G, (k X0 y) = (M.op X0 (M.op x y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq26800 X0
       grind)
    | exact superpose eq26800 eq28
    | (have j0 := eq28 X0 y
       grind)
    | exact resolve eq28 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27108 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26800 x
       grind)
    | exact superpose eq26800 eq18
    | (have j1 := eq26800 x
       grind)
    | exact resolve eq18 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27133 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq26683
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq26683
    | exact resolve eq26683 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27139 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15710 X0
       have i₂ := eq26800 sF0
       grind)
    | exact superpose eq26800 eq15710
    | (have j0 := eq15710 X0
       grind)
    | (have r₁ := eq15710 (M.op (M.op x y) (M.op x y))
       have r₂ := eq26800 (M.op x y)
       grind)
    | exact resolve eq15710 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15710
  have eq27172 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq27139 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq27139 (k (M.op x y) (M.op x y))
       have r₂ := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq27139 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq27139 (M.op x x)
       have r₂ := eq28 (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact resolve eq27139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27139
  have eq27180 : ∀ X0 : G, (M.op y (M.op x y)) = X0 ∨ (k X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq27074 X0
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq27074
    | (have j0 := eq27074 X0
       grind)
    | exact resolve eq27074 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27074
  have eq27186 : ∀ X0 : G, (k X0 y) = (M.op X0 (M.op x y)) ∨ x = X0 := by
    intro X0
    first
    | exact superpose eq27133 eq27180
    | (have j0 := eq27180 X0
       grind)
    | exact resolve eq27180 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27180
  have eq27205 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq27108 eq16178
    | exact resolve eq16178 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16178
  have eq27248 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq27108 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq27108
       grind)
    | exact resolve eq13 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27259 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq27248
  have eq27278 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq27205
    | exact resolve eq27205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27205
  have eq27329 : x ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq27133 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27331 : x = (k y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27133 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27338 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k x (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27133 eq16865
    | exact resolve eq16865 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865
  have eq27339 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27133 eq16866
    | exact resolve eq16866 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq27345 : y = (M.op y (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq27339
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq27339
    | exact resolve eq27339 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27339
  have eq27346 : ∀ X0 : G, y = (M.op y (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op X0 (k x (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27338 X0
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq27338
    | (have j0 := eq27338 X0
       grind)
    | exact resolve eq27338 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27338
  have eq27347 : x = (k y (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9963 eq27331
    | exact resolve eq27331 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27331
  have eq27348 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ x ≠ (M.op x y) := by
    first
    | (have i₁ := eq27329
       have i₂ := eq26800 sF0
       grind)
    | exact superpose eq26800 eq27329
    | exact resolve eq27329 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27329
  have eq27350 : x = y ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq27133 eq27345
    | exact resolve eq27345 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27345
  have eq27351 : x = y ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k x (M.op x y))) := by grind
  clear eq27350
  have eq27352 : ∀ X0 : G, x = y ∨ (M.op X0 (M.op x y)) = (M.op X0 (k x (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27133 eq27346
    | (have j0 := eq27346 X0
       grind)
    | exact resolve eq27346 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27346
  have eq27353 : ∀ X0 : G, x = y ∨ (M.op X0 (M.op x y)) = (M.op X0 (k x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq27352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27352
  have eq27354 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq27186 (M.op x y)
       grind)
    | (have r₁ := eq27348
       have r₂ := eq27186 (M.op x y)
       grind)
    | exact resolve eq27348 eq27186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348
  have eq27355 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq27172 eq27351
    | exact resolve eq27351 eq27172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27351
  have eq27356 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (k x (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27172 eq27353
    | exact resolve eq27353 eq27172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27353
  have eq27398 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (k (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq27354 eq188
    | exact resolve eq188 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq27409 : (M.op x y) ≠ (k (M.op x y) y) ∨ (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27354 eq13
    | exact resolve eq13 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27411 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq27354 eq28
    | exact resolve eq28 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27414 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (k (M.op x y) y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq27354 eq179
    | exact resolve eq179 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27423 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq27409
       have r₂ := eq27411
       grind)
    | exact resolve eq27409 eq27411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27409 eq27411
  have eq27427 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq27398 X0
       have i₂ := eq26800 X0
       grind)
    | exact superpose eq26800 eq27398
    | exact resolve eq27398 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27398
  have eq27439 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27423 eq27427
    | exact resolve eq27427 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27427
  have eq27454 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq27423 eq41
    | exact resolve eq41 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27461 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq27454
    | exact resolve eq27454 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27454
  have eq27467 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq27461
    | exact resolve eq27461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27461
  have eq27546 : (τ (σ (M.op x y))) = (k x (τ (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq27278 eq91
    | exact resolve eq91 eq27278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq27278
  have eq27566 : (M.op x y) = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29 eq27546
    | exact resolve eq27546 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27546
  have eq28016 : x ≠ (M.op (M.op x y) y) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq185 y
       have i₂ := eq26683
       grind)
    | exact superpose eq26683 eq185
    | (have j0 := eq185 y
       grind)
    | exact resolve eq185 eq26683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq26683
  have eq28021 : x ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq28016
       have i₂ := eq26800 sF0
       grind)
    | exact superpose eq26800 eq28016
    | exact resolve eq28016 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28016
  have eq28027 : x ≠ (k (M.op x y) y) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq27354 eq28021
    | exact resolve eq28021 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28021
  have eq28035 : x ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (M.op (M.op x y) y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq27423 eq28027
    | exact resolve eq28027 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28027
  have eq28037 : (M.op (M.op (M.op x y) (M.op x y)) y) = (k (M.op (M.op x y) (M.op x y)) y) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq28035
       have i₂ := eq26800 sF0
       grind)
    | exact superpose eq26800 eq28035
    | exact resolve eq28035 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq28039 : (M.op (k (M.op x y) y) y) = (k (k (M.op x y) y) y) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27354 eq28037
    | exact resolve eq28037 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28037
  have eq28041 : (M.op (k (M.op x y) (M.op x y)) y) = (k (k (M.op x y) (M.op x y)) y) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27423 eq28039
    | exact resolve eq28039 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28039
  have eq28043 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) y) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq28041
       have i₂ := eq26800 (k sF0 sF0)
       grind)
    | exact superpose eq26800 eq28041
    | exact resolve eq28041 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28041
  have eq28045 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (k (k (M.op x y) (M.op x y)) y) := by
    first
    | (have j1 := eq27186 (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq28043
       have r₂ := eq27186 (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq28043 eq27186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27186 eq28043
  have eq28738 : ∀ X0 : G, (k X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op x y)) ∨ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq27439 eq28
    | (have j0 := eq28 X0 (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq28 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28832 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = X0 ∨ (k X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27439 eq28738
    | (have j0 := eq28738 X0
       grind)
    | exact resolve eq28738 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28738
  have eq28838 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) y) = X0 ∨ (k X0 (k (M.op x y) (M.op x y))) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28045 eq28832
    | (have j0 := eq28832 X0
       grind)
    | exact resolve eq28832 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28832
  have eq29085 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op x y))) ∨ x = y := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f29085_13 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
      intro X0 X1 X2 X3
      grind
    have f29085_14 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y := by
      intro X0
      grind
    have f29085_23 : (M.op X2 X1) ≠ (M.op X2 (k (M.op X0 X1) (M.op x y))) := by grind
    have f29085_24 : x ≠ y := by grind
    have f29085_27 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
      intro X0
      first
      | (have j0 := f29085_14 X0
         grind)
      | (have r₁ := f29085_14 X0
         have r₂ := f29085_24
         grind)
      | exact resolve f29085_14 f29085_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29085_106 : (M.op X2 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op x y))) := by
      first
      | (have i₁ := f29085_23
         have i₂ := f29085_27 (M.op X0 X1)
         grind)
      | exact superpose f29085_27 f29085_23
      | exact resolve f29085_23 f29085_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f29085_109 : False := by
      first
      | (have r₁ := f29085_106
         have r₂ := f29085_13 (M.op x y) X1 X2 X0
         grind)
      | exact resolve f29085_106 f29085_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f29085_109
  clear eq179
  have eq29086 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (k (M.op X0 X1) (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq27172 eq16
    | exact resolve eq16 eq27172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29715 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27347 eq42
    | exact resolve eq42 eq27347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27347
  have eq29720 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq29715
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29715
    | exact resolve eq29715 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29715
  have eq29722 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq29720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29720
    | exact resolve eq29720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29720
  have eq29724 : x = (k (M.op x y) y) ∨ (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq27354 eq29722
    | exact resolve eq29722 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29722
  have eq29726 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27423 eq29724
    | exact resolve eq29724 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29724
  have eq29765 : (τ (σ x)) = (k y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29726 eq117
    | exact resolve eq117 eq29726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq29726
  have eq29773 : x = (k (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq30 eq29765
    | exact resolve eq29765 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29765
  have eq29899 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) y) ∨ (M.op (M.op x y) (k (M.op x y) (M.op x y))) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq28045 eq13
    | (have j0 := eq13 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29914 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq27439 eq29899
    | exact resolve eq29899 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899
  have eq29928 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have j1 := eq28838 (M.op x y)
       grind)
    | (have r₁ := eq29914
       have r₂ := eq28838 (M.op x y)
       grind)
    | exact resolve eq29914 eq28838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29914
  have eq29941 : (k (M.op x y) y) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq27354 eq29928
    | exact resolve eq29928 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29928
  have eq29950 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq27423 eq29941
    | exact resolve eq29941 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29941
  have eq29965 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq29950 eq38
    | exact resolve eq38 eq29950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq29950
  have eq29973 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq42 eq29965
    | exact resolve eq29965 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965
  have eq29979 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq29973
    | exact resolve eq29973 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29973
  have eq29983 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq27467 eq29979
    | exact resolve eq29979 eq27467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29979
  have eq30215 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq6279 eq192
    | (have r₁ := eq192 (M.op (σ x) (σ y))
       have r₂ := eq6279 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq192 eq6279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq30220 : (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq30215
  have eq31161 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (k (M.op x y) (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq27423 eq27414
    | exact resolve eq27414 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27414
  have eq31492 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (k (M.op x y) (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq28045 eq31161
    | exact resolve eq31161 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31161
  have eq31776 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k y y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20945 eq31492
    | exact resolve eq31492 eq20945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20945 eq31492
  have eq31883 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq31776 X0
       have i₂ := eq26756
       grind)
    | exact superpose eq26756 eq31776
    | exact resolve eq31776 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26756 eq31776
  have eq31886 : ∀ X0 : G, y = (M.op y (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31883 X0
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq31883
    | (have j0 := eq31883 X0
       grind)
    | exact resolve eq31883 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31883
  have eq31887 : ∀ X0 : G, x = y ∨ (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27133 eq31886
    | (have j0 := eq31886 X0
       grind)
    | exact resolve eq31886 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31886
  have eq31888 : ∀ X0 : G, x = y ∨ (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq31887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31887
  have eq31889 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 x) ∨ x = y ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27172 eq31888
    | exact resolve eq31888 eq27172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27172 eq31888
  have eq32450 : y ≠ (k (k (M.op x y) (M.op x y)) y) ∨ (k y (k (M.op x y) (M.op x y))) = (M.op y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq28045 eq27072
    | (have j0 := eq27072 (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq27072 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28045
  have eq32460 : y ≠ (k (M.op x y) y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq27354 eq27072
    | (have j0 := eq27072 (M.op x y)
       grind)
    | exact resolve eq27072 eq27354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27072 eq27354
  have eq32467 : y ≠ (k (M.op x y) (M.op x y)) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq27423 eq32460
    | exact resolve eq32460 eq27423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27423 eq32460
  have eq32470 : (M.op y (M.op x y)) = (k y (k (M.op x y) (M.op x y))) ∨ y ≠ (k (k (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq27439 eq32450
    | exact resolve eq32450 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27439 eq32450
  have eq32475 : x = (k y (M.op x y)) ∨ y ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27133 eq32467
    | exact resolve eq32467 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32467
  have eq32478 : (M.op y (M.op x y)) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | (have j1 := eq28838 y
       grind)
    | (have r₁ := eq32470
       have r₂ := eq28838 y
       grind)
    | exact resolve eq32470 eq28838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28838 eq32470
  have eq32483 : x = (k y (M.op x y)) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9963 eq32475
    | exact resolve eq32475 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9963 eq32475
  have eq32486 : x = (k y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq27133 eq32478
    | exact resolve eq32478 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32478
  have eq32490 : x = (k y (M.op x y)) := by
    first
    | (have r₁ := eq32483
       have r₂ := eq29773
       grind)
    | exact resolve eq32483 eq29773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29773 eq32483
  have eq32523 : (σ x) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq32486 eq37
    | exact resolve eq37 eq32486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32486
  have eq32530 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq42 eq32523
    | exact resolve eq32523 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32523
  have eq32531 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq32530
    | exact resolve eq32530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32530
  have eq32532 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq27467 eq32531
    | exact resolve eq32531 eq27467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32531
  have eq32533 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq32532
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32532
    | exact resolve eq32532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32532
  have eq38750 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq30220 eq6279
    | exact resolve eq6279 eq30220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6279 eq30220
  have eq38769 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq38750
  have eq55089 : (k x y) = (k y (M.op x y)) ∨ x = y ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq31889 y
       have i₂ := eq24327
       grind)
    | exact superpose eq24327 eq31889
    | exact resolve eq31889 eq24327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24327 eq31889
  have eq55373 : x = (k x y) ∨ x = y ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq32490 eq55089
    | exact resolve eq55089 eq32490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32490 eq55089
  have eq55415 : x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq55373
       have r₂ := eq24426
       grind)
    | exact resolve eq55373 eq24426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24426 eq55373
  have eq57277 : x = (M.op y x) ∨ x = y ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq55415 eq24024
    | exact resolve eq24024 eq55415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024 eq55415
  have eq57333 : x = (M.op y x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq57277
  have eq57369 : y = (M.op y (M.op x y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq57333
       have i₂ := eq26800 y
       grind)
    | exact superpose eq26800 eq57333
    | exact resolve eq57333 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57333
  have eq57386 : x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27133 eq57369
    | exact resolve eq57369 eq27133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57369
  have eq57387 : x = (M.op y x) ∨ x = y := by grind
  clear eq57386
  have eq57412 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq57387
       grind)
    | exact superpose eq57387 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq57387
       grind)
    | exact resolve eq13 eq57387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57414 : y = (M.op x x) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq57387
       grind)
    | exact superpose eq57387 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq57387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq57427 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (k x (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29085 y x X0
       have i₂ := eq57387
       grind)
    | exact superpose eq57387 eq29085
    | exact resolve eq29085 eq57387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29085
  have eq57428 : (M.op (M.op x y) x) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq29086 y x
       have i₂ := eq57387
       grind)
    | exact superpose eq57387 eq29086
    | exact resolve eq29086 eq57387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29086 eq57387
  have eq57429 : (M.op (M.op x y) x) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y := by grind
  clear eq57428
  have eq57430 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (k x (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq57427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57427
  have eq57433 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq57412
  have eq57444 : (k (M.op x y) x) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq27259 eq57429
    | exact resolve eq57429 eq27259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27259 eq57429
  have eq57445 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27356 eq57430
    | exact resolve eq57430 eq27356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27356 eq57430
  have eq57453 : (k x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq57433
       have i₂ := eq26800 x
       grind)
    | exact superpose eq26800 eq57433
    | exact resolve eq57433 eq26800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26800 eq57433
  have eq57455 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq27355 eq57444
    | exact resolve eq57444 eq27355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27355 eq57444
  have eq57464 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq27108 eq57453
    | exact resolve eq57453 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57453
  have eq57480 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq57464
       grind)
    | exact superpose eq57464 eq41
    | exact resolve eq41 eq57464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57464
  have eq57493 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57480
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57480
    | exact resolve eq57480 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57480
  have eq57497 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq57493
    | exact resolve eq57493 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57493
  have eq57926 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq57455 eq40
    | exact resolve eq40 eq57455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq57455
  have eq57965 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq42 eq57926
    | exact resolve eq57926 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq57926
  have eq57984 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq57965
    | exact resolve eq57965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57965
  have eq57993 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27467 eq57984
    | exact resolve eq57984 eq27467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27467 eq57984
  have eq58035 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq57993 eq29983
    | exact resolve eq29983 eq57993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29983
  have eq58037 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq57993 eq32533
    | exact resolve eq32533 eq57993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32533 eq57993
  have eq58331 : y = (k x (M.op x y)) ∨ x = y ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq57445 x
       have i₂ := eq57414
       grind)
    | exact superpose eq57414 eq57445
    | exact resolve eq57445 eq57414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57414 eq57445
  have eq58367 : y = (k x (M.op x y)) ∨ x = y ∨ x = (k y x) := by grind
  clear eq58331
  have eq58407 : x = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27566 eq58367
    | exact resolve eq58367 eq27566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27566 eq58367
  have eq58450 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq58407
       grind)
    | exact superpose eq58407 eq37
    | exact resolve eq37 eq58407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq58452 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1201 y x
       have i₂ := eq58407
       grind)
    | exact superpose eq58407 eq1201
    | (have j0 := eq1201 y x
       grind)
    | exact resolve eq1201 eq58407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq58407
  have eq58459 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq58452
  have eq58469 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58459
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq58459
    | exact resolve eq58459 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq58459
  have eq58471 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58450
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58450
    | exact resolve eq58450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58450
  have eq58481 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58469
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58469
    | exact resolve eq58469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58469
  have eq58486 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58481
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58481
    | exact resolve eq58481 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58481
  have eq58487 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq58486
    | exact resolve eq58486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58486
  have eq58488 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58487
    | exact resolve eq58487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58487
  have eq58489 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58488
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58488
    | exact resolve eq58488 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58488
  have eq58490 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq57497 eq58489
    | exact resolve eq58489 eq57497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58489
  have eq58491 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58490
       have r₂ := eq27
       grind)
    | exact resolve eq58490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58490
  have eq58532 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58491 eq6445
    | exact resolve eq6445 eq58491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58491
  have eq58572 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq58532
  have eq58585 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58471 eq58572
    | exact resolve eq58572 eq58471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58471 eq58572
  have eq58785 : (M.op (M.op (σ y) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58585 eq38769
    | exact resolve eq38769 eq58585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38769 eq58585
  have eq58788 : (M.op (M.op (σ y) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq58785
  have eq58839 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6254 eq58788
    | exact resolve eq58788 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254 eq58788
  have eq58877 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq58839
    | exact resolve eq58839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58839
  have eq58895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57497 eq58877
    | exact resolve eq58877 eq57497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58877
  have eq58904 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58895
       have r₂ := eq27
       grind)
    | exact resolve eq58895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58895
  have eq58962 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58904 eq6719
    | (have r₁ := eq6719
       have r₂ := eq58904
       grind)
    | exact resolve eq6719 eq58904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58904
  have eq59065 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq58962
  have eq59066 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq59065
  have eq59113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq59066
    | exact resolve eq59066 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59066
  have eq59143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq57497 eq59113
    | exact resolve eq59113 eq57497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59113
  have eq59153 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq59143
       have r₂ := eq27
       grind)
    | exact resolve eq59143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59143
  have eq59160 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq59153
       grind)
    | exact superpose eq59153 eq24
    | exact resolve eq24 eq59153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59153
  have eq59314 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq59160
    | exact resolve eq59160 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59160
  have eq59483 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq59314 eq58035
    | exact resolve eq58035 eq59314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58035
  have eq59484 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq59314 eq58037
    | exact resolve eq58037 eq59314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58037
  have eq59485 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ x = y := by grind
  clear eq59484
  have eq59486 : (k (σ y) (σ x)) = (k (σ y) (k (σ y) (σ x))) ∨ x = y := by grind
  clear eq59483
  have eq59553 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq59485 eq59486
    | exact resolve eq59486 eq59485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59486
  have eq62660 : (σ x) ≠ (k (σ y) (σ x)) ∨ (M.op (k (σ y) (σ x)) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq59485 eq607
    | (have j0 := eq607 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq607 eq59485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq59485
  have eq62679 : (M.op (k (σ y) (σ x)) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | (have r₁ := eq62660
       have r₂ := eq59553
       grind)
    | exact resolve eq62660 eq59553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62660
  have eq62688 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq59553 eq62679
    | exact resolve eq62679 eq59553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62679
  have eq62695 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq26 eq62688
    | exact resolve eq62688 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62688
  have eq62699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq57497 eq62695
    | exact resolve eq62695 eq57497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62695
  have eq62702 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | (have r₁ := eq62699
       have r₂ := eq27
       grind)
    | exact resolve eq62699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62699
  have eq62704 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq59553 eq62702
    | exact resolve eq62702 eq59553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62702
  have eq62715 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq62704 eq6445
    | exact resolve eq6445 eq62704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445 eq62704
  have eq62755 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq62715
  have eq62767 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq59553 eq62755
    | exact resolve eq62755 eq59553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59553 eq62755
  have eq62785 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq62767 eq27
    | exact resolve eq27 eq62767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62767
  have eq62974 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq62785
       have r₂ := eq59314
       grind)
    | exact resolve eq62785 eq59314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59314 eq62785
  have eq63050 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq62974 eq6719
    | (have r₁ := eq6719
       have r₂ := eq62974
       grind)
    | exact resolve eq6719 eq62974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6719 eq62974
  have eq63155 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq63050
  have eq63156 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq63155
  have eq63206 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq63156
    | exact resolve eq63156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63156
  have eq63233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq57497 eq63206
    | exact resolve eq63206 eq57497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57497 eq63206
  have eq63248 : x = y := by
    first
    | (have r₁ := eq63233
       have r₂ := eq27
       grind)
    | exact resolve eq63233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63233
  have eq63263 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq63248
       grind)
    | exact superpose eq63248 eq24
    | exact resolve eq24 eq63248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq63302 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq27133
       have i₂ := eq63248
       grind)
    | exact superpose eq63248 eq27133
    | exact resolve eq27133 eq63248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27133 eq63248
  have eq63338 : x = (M.op x y) := by
    first
    | exact superpose eq27108 eq63302
    | exact resolve eq63302 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27108 eq63302
  have eq63363 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63263
    | exact resolve eq63263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63263
  have eq63395 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq63338
       grind)
    | exact superpose eq63338 eq22
    | exact resolve eq22 eq63338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq63338
  have eq63639 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63363 eq26
    | exact resolve eq26 eq63363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq63745 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63363 eq26775
    | (have r₁ := eq26775
       have r₂ := eq63363
       grind)
    | exact resolve eq26775 eq63363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26775 eq63363
  have eq63789 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq63745
  have eq63820 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63789 eq63639
    | exact resolve eq63639 eq63789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63639 eq63789
  have eq64015 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq63820 eq27
    | exact resolve eq27 eq63820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63820
  have eq64153 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq63395 eq20
    | exact resolve eq20 eq63395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq63395
  have eq64220 : False := by grind
  exact eq64220

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k (k y (M.op x y)) X0)) = (k (k (σ y) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq76 eq10
    | exact resolve eq10 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0) (σ X1)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq45
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 y y
       grind)
    | exact superpose eq77 eq75
    | (have j1 := eq77 y y
       grind)
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq77 x sF0
       grind)
    | exact superpose eq77 eq46
    | (have j1 := eq77 x (M.op x y)
       grind)
    | exact resolve eq46 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq104 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq77 y sF0
       grind)
    | exact superpose eq77 eq76
    | (have j1 := eq77 y (M.op x y)
       grind)
    | exact resolve eq76 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq125 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq38
  have eq138 : (σ (k y (k (M.op x y) y))) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq125 eq37
    | exact resolve eq37 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (k x (k (M.op x y) y))) = (k (σ x) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq125 eq36
    | exact resolve eq36 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq77 (σ X0) sF3
       grind)
    | exact superpose eq77 eq41
    | (have j1 := eq77 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op (M.op x y) X0) X0) = (k (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op (M.op x y) X0) X0
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq206 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq204
    | exact resolve eq204 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq231 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq297 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq77 (τ X0) X1
       grind)
    | exact superpose eq77 eq35
    | (have j1 := eq77 (τ X0) X1
       grind)
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq41
    | exact resolve eq41 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq323 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq335 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq439 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X3) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq55 X3 X1 X0 X2
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) X3) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X1) (M.op X3 X1)
       have r₂ := eq55 X1 X1 (M.op X3 X1) X3
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq93 X0 X0
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq575 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq570
    | (have j0 := eq570 X0 X1
       grind)
    | exact resolve eq570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq614 : ∀ X0 : G, (k (k x y) (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq335 (k x y) X0
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq335
    | exact resolve eq335 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq110 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq657
    | exact resolve eq657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq661 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq658
       have r₂ := eq28
       grind)
    | exact resolve eq658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq663 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq661 eq55
    | exact resolve eq55 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  have eq737 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq666 eq110
    | exact resolve eq110 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq666 eq59
    | exact resolve eq59 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq740 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq737
  have eq742 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq738
    | exact resolve eq738 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq745 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq740 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq740
       grind)
    | exact resolve eq13 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq745
  have eq748 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq747
    | exact resolve eq747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq748 eq110
    | exact resolve eq110 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq753
  have eq760 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq756
       have r₂ := eq28
       grind)
    | exact resolve eq756 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq764 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0 y
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq55
    | exact resolve eq55 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq764 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq764
    | (have j0 := eq764 X0 y
       grind)
    | exact resolve eq764 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq831 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq742 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq742
       grind)
    | exact resolve eq13 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq833 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq831
  have eq834 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq833
    | exact resolve eq833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq834 eq110
    | exact resolve eq110 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq841
  have eq848 : x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq844
       have r₂ := eq28
       grind)
    | exact resolve eq844 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq891 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq848
       grind)
    | exact superpose eq848 eq45
    | exact resolve eq45 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77 x y
       have i₂ := eq848
       grind)
    | exact superpose eq848 eq77
    | (have j0 := eq77 x y
       grind)
    | exact resolve eq77 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq892
  have eq895 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq893
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq893
    | exact resolve eq893 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq896 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq891
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq891
    | exact resolve eq891 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1129 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ y)) = (σ (M.op (k (τ X0) X1) y)) ∨ (k (τ X0) X1) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq77 (k (τ X0) X1) y
       grind)
    | exact superpose eq77 eq305
    | (have j1 := eq77 (k (τ X0) X1) y
       grind)
    | exact resolve eq305 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq2109 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (k (σ y) (σ X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq182 eq13
    | (have j0 := eq13 (σ y) (σ X0)
       have j1 := eq182 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq182 y
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2111 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq2109
    | (have j0 := eq2109 X0
       grind)
    | exact resolve eq2109 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq4838 : ∀ X0 X1 : G, (σ (M.op (τ X0) y)) = (k X0 (σ (M.op (M.op x y) X1))) ∨ (τ X0) = (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq206 eq297
    | (have j0 := eq297 X0 (M.op (M.op x y) X1)
       grind)
    | exact resolve eq297 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4844 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq767 eq297
    | (have j0 := eq297 X0 (M.op x y)
       grind)
    | exact resolve eq297 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq4879 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq4844
    | (have j0 := eq4844 X0
       grind)
    | exact resolve eq4844 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq4883 : ∀ X0 X1 : G, (σ (M.op (τ X0) y)) = (k X0 (σ (M.op (M.op x y) X1))) ∨ (τ X0) = (M.op (M.op (M.op x y) X1) y) := by
    intro X0 X1
    first
    | exact superpose eq206 eq4838
    | (have j0 := eq4838 X0 X1
       grind)
    | exact resolve eq4838 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4838
  have eq6648 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = (k (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq439 (M.op X0 X1) X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq8893 : ∀ X0 X1 : G, (σ (k (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) X1)) = (k (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X1)) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq298 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0 X1
       have i₂ := eq323 (σ X0)
       grind)
    | exact superpose eq323 eq298
    | (have j1 := eq323 (σ X0)
       grind)
    | exact resolve eq298 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq323
  have eq8933 : ∀ X0 X1 : G, (σ (k (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) X1)) = (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X1)) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8893 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0))) X1
       grind)
    | exact superpose eq10 eq8893
    | (have j0 := eq8893 X0 X1
       grind)
    | exact resolve eq8893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8893
  have eq8975 : ∀ X0 X1 : G, (σ (k (k (τ (σ (M.op X0 X0))) X0) X1)) = (σ (k (M.op X0 X0) X1)) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8933 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq8933
    | (have j0 := eq8933 X0 X1
       grind)
    | exact resolve eq8933 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8933
  have eq9001 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (σ (k (k (M.op X0 X0) X0) X1)) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8975 X0 X1
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq8975
    | (have j0 := eq8975 X0 X1
       grind)
    | exact resolve eq8975 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8975
  have eq9014 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (σ (k (k (M.op X0 X0) X0) X1)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9001 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq9001
    | (have j0 := eq9001 X0 X1
       grind)
    | exact resolve eq9001 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001
  have eq9064 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq4879
    | exact resolve eq4879 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4879
  have eq9663 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9064
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq9064
    | exact resolve eq9064 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064
  have eq9706 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9663
  have eq9708 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9706
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9706
    | exact resolve eq9706 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9706
  have eq9711 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9708 eq92
    | exact resolve eq92 eq9708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9708
  have eq9715 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq9711
    | exact resolve eq9711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711
  have eq9793 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9715 eq767
    | exact resolve eq767 eq9715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9715
  have eq9802 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) := by grind
  clear eq9793
  have eq9810 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq9802 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq9802
       grind)
    | exact resolve eq13 eq9802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9802
  have eq9817 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) := by grind
  clear eq9810
  have eq9916 : x ≠ (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) := by grind
  clear eq9817
  have eq9929 : x ≠ (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq767 eq9916
    | exact resolve eq9916 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq9916
  have eq9930 : x ≠ (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y (M.op x y)) := by grind
  clear eq9929
  have eq9931 : x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq9930
       have r₂ := eq760
       grind)
    | exact resolve eq9930 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9930
  have eq10025 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9931 eq76
    | exact resolve eq76 eq9931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9931
  have eq10034 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10025
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10025
    | exact resolve eq10025 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10025
  have eq10039 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10034
       have i₂ := eq77 sF3 sF1
       grind)
    | exact superpose eq77 eq10034
    | (have j1 := eq77 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq10034 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10034
  have eq28526 : ∀ X0 : G, (k x (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq848
       grind)
    | exact superpose eq848 eq614
    | exact resolve eq614 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq848
  have eq28639 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (k (k (σ x) (σ y)) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq28526 X0
       have i₂ := eq231 X0
       grind)
    | exact superpose eq231 eq28526
    | exact resolve eq28526 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq28526
  have eq56629 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq110 eq28639
    | exact resolve eq28639 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28639
  have eq56777 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq56629 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56629
  have eq56913 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq896 eq56777
    | exact resolve eq56777 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq56777
  have eq57040 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq56913
  have eq57137 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq142 eq57040
    | exact resolve eq57040 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57040
  have eq57152 : x = (k (M.op x y) y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq57137
    | exact resolve eq57137 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57137
  have eq57165 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq57152
       have i₂ := eq77 sF0 y
       grind)
    | exact superpose eq77 eq57152
    | (have j1 := eq77 (M.op x y) y
       grind)
    | exact resolve eq57152 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57152
  have eq95998 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq57165
  have eq96002 : x = (M.op (M.op x y) y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq95998
       have r₂ := eq895
       grind)
    | exact resolve eq95998 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95998
  have eq96019 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq96002 eq206
    | exact resolve eq206 eq96002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96002
  have eq96038 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96019 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96019
    | (have j0 := eq96019 x
       grind)
    | exact resolve eq96019 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96019
  have eq96156 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq96038
       grind)
    | exact superpose eq96038 eq13
    | exact resolve eq13 eq96038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96038
  have eq96167 : (M.op x y) = (k x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq96156
       have r₂ := eq895
       grind)
    | exact resolve eq96156 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq96156
  have eq96261 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq573 x
       have i₂ := eq96167
       grind)
    | exact superpose eq96167 eq573
    | (have j0 := eq573 x
       grind)
    | exact resolve eq573 eq96167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq96167
  have eq96275 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96261
    | exact resolve eq96261 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96261
  have eq96292 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96275
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96275
    | exact resolve eq96275 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96275
  have eq96298 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq96292
       have r₂ := eq760
       grind)
    | exact resolve eq96292 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq96292
  have eq96302 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96298
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96298
    | exact resolve eq96298 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96298
  have eq96451 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq96302 eq663
    | exact resolve eq663 eq96302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq96302
  have eq96464 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq96451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96451
  have eq106054 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq96464 eq661
    | exact resolve eq661 eq96464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq96464
  have eq106075 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq106054
  have eq106139 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq106075 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq106075
       grind)
    | exact resolve eq13 eq106075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106075
  have eq106148 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq106139
  have eq106154 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq106148
    | exact resolve eq106148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106148
  have eq106169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq106154 eq110
    | exact resolve eq110 eq106154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq106154
  have eq106257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq106169
  have eq106263 : x = (M.op y y) := by
    first
    | (have r₁ := eq106257
       have r₂ := eq28
       grind)
    | exact resolve eq106257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106257
  have eq106267 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq102
    | exact resolve eq102 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106275 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq13
    | exact resolve eq13 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106276 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq14
    | exact resolve eq14 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106286 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq106267
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq106267
    | exact resolve eq106267 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106267
  have eq106294 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq106286 eq87
    | exact resolve eq87 eq106286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq106286
  have eq106315 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq106294
    | exact resolve eq106294 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106294
  have eq106318 : x = (k y y) := by
    first
    | (have r₁ := eq106315
       have r₂ := eq106275
       grind)
    | exact resolve eq106315 eq106275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106275 eq106315
  have eq106321 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq106318
       grind)
    | exact superpose eq106318 eq75
    | exact resolve eq75 eq106318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq106318
  have eq106363 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq106321
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq106321
    | exact resolve eq106321 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106321
  have eq106382 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106363
       have i₂ := eq77 sF3 sF3
       grind)
    | exact superpose eq77 eq106363
    | (have j1 := eq77 (σ y) (σ y)
       grind)
    | exact resolve eq106363 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106800 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq106276 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106276
    | (have j0 := eq106276 y
       grind)
    | exact resolve eq106276 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106930 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq106800
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq106800
    | exact resolve eq106800 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106800
  have eq107340 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq106930 eq104
    | exact resolve eq104 eq106930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq107351 : x ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq106930 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq106930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107352 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq106930 eq14
    | exact resolve eq14 eq106930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106930
  have eq107364 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq107352 X0
       have i₂ := eq106276 X0
       grind)
    | exact superpose eq106276 eq107352
    | exact resolve eq107352 eq106276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106276 eq107352
  have eq107365 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq107340
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107340
    | exact resolve eq107340 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107340
  have eq107421 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq107364 eq103
    | exact resolve eq103 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107442 : (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq107364 eq203
    | (have r₁ := eq203 (M.op x y)
       have r₂ := eq107364 (M.op x y)
       grind)
    | exact resolve eq203 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107457 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by grind
  clear eq107442
  have eq107458 : (k (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq107364 eq107457
    | exact resolve eq107457 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107457
  have eq107461 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq107421
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107421
    | exact resolve eq107421 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107421
  have eq107484 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq107461
    | exact resolve eq107461 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107461
  have eq107495 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq107364 eq107484
    | exact resolve eq107484 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107484
  have eq109771 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq107364 eq107365
    | exact resolve eq107365 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107365
  have eq109776 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq109771 eq92
    | exact resolve eq92 eq109771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109771
  have eq109790 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq109776
    | exact resolve eq109776 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109776
  have eq109810 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq106382 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq106382
       grind)
    | exact resolve eq13 eq106382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109819 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq106382
  have eq109820 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq109810
  have eq109821 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq106363 eq109820
    | exact resolve eq109820 eq106363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106363 eq109820
  have eq110222 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq109821
       have r₂ := eq109819
       grind)
    | exact resolve eq109821 eq109819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109819 eq109821
  have eq110237 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  have eq110240 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq110222 eq55
    | exact resolve eq55 eq110222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112292 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq107495
       have i₂ := eq77 sF2 sF1
       grind)
    | exact superpose eq77 eq107495
    | (have j1 := eq77 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq107495 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107495
  have eq112356 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq109790 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq109790
       grind)
    | exact resolve eq13 eq109790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109790
  have eq112365 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq112356
  have eq112367 : (k y (M.op x y)) = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq107364 eq112365
    | exact resolve eq112365 eq107364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107364 eq112365
  have eq112375 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq112367
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq112367
    | exact resolve eq112367 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112367
  have eq112376 : x = (k y (M.op x y)) := by grind
  clear eq112375
  have eq112390 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq112376 eq76
    | exact resolve eq76 eq112376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112441 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq112390
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112390
    | exact resolve eq112390 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112390
  have eq112459 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq112441
       have i₂ := eq77 sF3 sF1
       grind)
    | exact superpose eq77 eq112441
    | (have j1 := eq77 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq112441 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113379 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq110237 eq59
    | exact resolve eq59 eq110237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq110237
  have eq113417 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq113379
    | exact resolve eq113379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113379
  have eq113422 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq112459
  have eq113433 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq112441 eq113422
    | exact resolve eq113422 eq112441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113422
  have eq113851 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq113417 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq113417
       grind)
    | exact resolve eq13 eq113417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113417
  have eq113860 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq113851
  have eq113868 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq27 eq113860
    | exact resolve eq113860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113860
  have eq145512 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq113433 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq113433
       grind)
    | exact resolve eq13 eq113433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113433
  have eq145521 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq145512
  have eq145527 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq112441 eq145521
    | exact resolve eq145521 eq112441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145521
  have eq145528 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq145527
  have eq145533 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq145528 eq55
    | exact resolve eq55 eq145528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145528
  have eq145541 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq110240 eq145533
    | exact resolve eq145533 eq110240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145533
  have eq145548 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq145541
    | (have j0 := eq145541 (σ x)
       grind)
    | exact resolve eq145541 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145541
  have eq182758 : ∀ X0 : G, (σ (M.op (τ (k (σ y) (σ (M.op x y)))) y)) = (σ (k (k y (M.op x y)) (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq4883 eq91
    | (have j1 := eq4883 (k (σ y) (σ (M.op x y))) X0
       grind)
    | exact resolve eq91 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq182782 : ∀ X0 : G, (σ (M.op (τ (σ y)) y)) = (σ (k y (M.op (M.op x y) X0))) ∨ (τ (σ y)) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq4883 eq37
    | (have j1 := eq4883 (σ y) X0
       grind)
    | exact resolve eq37 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4883
  have eq183035 : ∀ X0 : G, (σ (M.op y y)) = (σ (k y (M.op (M.op x y) X0))) ∨ (τ (σ y)) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq30 eq182782
    | (have j0 := eq182782 X0
       grind)
    | exact resolve eq182782 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182782
  have eq183053 : ∀ X0 : G, (σ (M.op (τ (k (σ y) (σ (M.op x y)))) y)) = (σ (k x (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq112376 eq182758
    | (have j0 := eq182758 X0
       grind)
    | exact resolve eq182758 eq112376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182758
  have eq183215 : ∀ X0 : G, (σ x) = (σ (k y (M.op (M.op x y) X0))) ∨ (τ (σ y)) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq183035 X0
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq183035
    | (have j0 := eq183035 X0
       grind)
    | exact resolve eq183035 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183035
  have eq183233 : ∀ X0 : G, (σ (M.op (k y (M.op x y)) y)) = (σ (k x (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq92 eq183053
    | (have j0 := eq183053 X0
       grind)
    | exact resolve eq183053 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183053
  have eq183366 : ∀ X0 : G, (σ x) = (σ (k y (M.op (M.op x y) X0))) ∨ (τ (σ y)) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq183215 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq183215
    | (have j0 := eq183215 X0
       grind)
    | exact resolve eq183215 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183215
  have eq183368 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq112376 eq183233
    | (have j0 := eq183233 X0
       grind)
    | exact resolve eq183233 eq112376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183233
  have eq183443 : ∀ X0 : G, (σ x) = (σ (k y (M.op (M.op x y) X0))) ∨ y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq30 eq183366
    | (have j0 := eq183366 X0
       grind)
    | exact resolve eq183366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq183366
  have eq183445 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq183368 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq183368
    | (have j0 := eq183368 X0
       grind)
    | exact resolve eq183368 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183368
  have eq183504 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op (M.op x y) X0))) ∨ (τ (k (σ y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq21 eq183445
    | (have j0 := eq183445 X0
       grind)
    | exact resolve eq183445 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183445
  have eq183529 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op (M.op x y) X0) y) ∨ (σ (M.op x y)) = (σ (k x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq92 eq183504
    | (have j0 := eq183504 X0
       grind)
    | exact resolve eq183504 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq183504
  have eq183546 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op (M.op x y) X0))) ∨ x = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq112376 eq183529
    | (have j0 := eq183529 X0
       grind)
    | exact resolve eq183529 eq112376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112376 eq183529
  have eq183657 : ∀ X0 : G, (τ (σ x)) = (k y (M.op (M.op x y) X0)) ∨ y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq183443 eq16
    | (have j1 := eq183443 X0
       grind)
    | exact resolve eq16 eq183443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183443
  have eq183782 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq29 eq183657
    | (have j0 := eq183657 X0
       grind)
    | exact resolve eq183657 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183657
  have eq183900 : ∀ X0 : G, y ≠ y ∨ (k y (M.op (M.op x y) X0)) = (M.op y (M.op (M.op x y) X0)) ∨ x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq183782 eq13
    | (have j0 := eq13 y (M.op (M.op x y) X0)
       have j1 := eq183782 X0
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) X0)
       have r₂ := eq183782 X0
       grind)
    | exact resolve eq13 eq183782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183782
  have eq183912 : ∀ X0 : G, (k y (M.op (M.op x y) X0)) = (M.op y (M.op (M.op x y) X0)) ∨ x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq183900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183900
  have eq183916 : ∀ X0 : G, (M.op y y) = (k y (M.op (M.op x y) X0)) ∨ x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq206 eq183912
    | (have j0 := eq183912 X0
       grind)
    | exact resolve eq183912 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183912
  have eq183928 : ∀ X0 : G, x = (k y (M.op (M.op x y) X0)) ∨ x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq183916 X0
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq183916
    | (have j0 := eq183916 X0
       grind)
    | exact resolve eq183916 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183916
  have eq183929 : ∀ X0 : G, x = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq183928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183928
  have eq185119 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq183546 eq16
    | (have j1 := eq183546 X0
       grind)
    | exact resolve eq16 eq183546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185250 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq31 eq185119
    | (have j0 := eq185119 X0
       grind)
    | exact resolve eq185119 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185119
  have eq191094 : ∀ X0 : G, (σ y) ≠ (σ (k X0 y)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq110222 eq2111
    | (have j0 := eq2111 X0
       grind)
    | exact resolve eq2111 eq110222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq191681 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (k y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq125 eq191094
    | (have j0 := eq191094 (M.op x y)
       grind)
    | exact resolve eq191094 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191094
  have eq191687 : (σ (k y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq191681
    | exact resolve eq191681 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191681
  have eq191764 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76 eq191687
    | exact resolve eq191687 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq191687
  have eq191839 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq112441 eq191764
    | exact resolve eq191764 eq112441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191764
  have eq191894 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq191839
    | exact resolve eq191839 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191839
  have eq191967 : (σ y) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191894
       have i₂ := eq77 sF1 sF3
       grind)
    | exact superpose eq77 eq191894
    | (have j1 := eq77 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq191894 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191894
  have eq191968 : (σ (M.op x y)) = (σ x) ∨ (σ y) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq110222 eq191967
    | exact resolve eq191967 eq110222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191967
  have eq191969 : (σ y) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq191968
  have eq209465 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ y)) = (σ (M.op (k (τ X0) X1) y)) ∨ x = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 X1
       have i₂ := eq106263
       grind)
    | exact superpose eq106263 eq1129
    | (have j0 := eq1129 X0 X1
       grind)
    | exact resolve eq1129 eq106263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq106263
  have eq209580 : ∀ X0 : G, (k (k (σ x) (σ X0)) (σ y)) = (σ (M.op (k x X0) y)) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq29 eq209465
    | exact resolve eq209465 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209465
  have eq209856 : ∀ X0 : G, (k (σ (k x X0)) (σ y)) = (σ (M.op (k x X0) y)) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq36 eq209580
    | (have j0 := eq209580 X0
       grind)
    | exact resolve eq209580 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq209580
  have eq209943 : ∀ X0 : G, (σ (k (k x X0) y)) = (σ (M.op (k x X0) y)) ∨ x = (k x X0) := by
    intro X0
    first
    | exact superpose eq41 eq209856
    | (have j0 := eq209856 X0
       grind)
    | exact resolve eq209856 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq209856
  have eq333949 : ∀ X0 : G, (σ (k (σ y) X0)) = (σ (k (k (σ y) (σ (M.op x y))) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10039 eq9014
    | exact resolve eq9014 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014 eq10039
  have eq334522 : ∀ X0 : G, (σ (k (σ y) X0)) = (σ (k (k (σ y) (σ (M.op x y))) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq333949 X0
       grind)
    | (have r₁ := eq333949 X0
       have r₂ := eq191969
       grind)
    | exact resolve eq333949 eq191969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191969 eq333949
  have eq334616 : ∀ X0 : G, (σ (k (σ x) X0)) = (σ (k (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq112441 eq334522
    | exact resolve eq334522 eq112441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112441 eq334522
  have eq1354295 : ∀ X0 : G, (k (k x X0) y) = (τ (σ (M.op (k x X0) y))) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq16 (k (k x X0) y)
       have i₂ := eq209943 X0
       grind)
    | exact superpose eq209943 eq16
    | (have j1 := eq209943 X0
       grind)
    | exact resolve eq16 eq209943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209943
  have eq1354775 : ∀ X0 : G, (k (k x X0) y) = (M.op (k x X0) y) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq1354295 X0
       have i₂ := eq16 (M.op (k x X0) y)
       grind)
    | exact superpose eq16 eq1354295
    | (have j0 := eq1354295 X0
       grind)
    | exact resolve eq1354295 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354295
  have eq1361265 : ∀ X0 : G, (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq185250 eq1354775
    | (have j1 := eq185250 X0
       grind)
    | exact resolve eq1354775 eq185250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185250
  have eq1361608 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have j0 := eq1361265 X0
       grind)
    | (have r₁ := eq1361265 X0
       have r₂ := eq107351
       grind)
    | exact resolve eq1361265 eq107351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361265
  have eq1362878 : (k x (M.op (M.op x y) y)) = (M.op x (M.op (M.op x y) y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1361608 eq6648
    | exact resolve eq6648 eq1361608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361608
  have eq1362982 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq206 eq1362878
    | exact resolve eq1362878 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362878
  have eq1362997 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1362982
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1362982
    | exact resolve eq1362982 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362982
  have eq1365138 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1362997 eq1354775
    | exact resolve eq1354775 eq1362997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354775 eq1362997
  have eq1365180 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq1365138
  have eq1365222 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq1365180
       have r₂ := eq107351
       grind)
    | exact resolve eq1365180 eq107351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107351 eq1365180
  have eq1365358 : (k (σ y) (k (σ (M.op x y)) (σ y))) = (σ (k y (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1365222 eq138
    | exact resolve eq138 eq1365222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1365359 : (k (σ x) (k (σ (M.op x y)) (σ y))) = (σ (k x (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1365222 eq139
    | exact resolve eq139 eq1365222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1365553 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq183929 eq1365358
    | exact resolve eq1365358 eq183929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183929 eq1365358
  have eq1365609 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq1365553
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1365553
    | exact resolve eq1365553 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365553
  have eq1368866 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ x = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq183546 eq1365359
    | (have j1 := eq183546 y
       grind)
    | exact resolve eq1365359 eq183546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183546
  have eq1747570 : ∀ X0 : G, (k (σ y) X0) = (τ (σ (k (σ x) X0))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq334616 eq16
    | exact resolve eq16 eq334616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334616
  have eq1748164 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1747570 X0
       have i₂ := eq16 (k sF2 X0)
       grind)
    | exact superpose eq16 eq1747570
    | exact resolve eq1747570 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747570
  have eq1751975 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1365609 eq1748164
    | exact resolve eq1748164 eq1365609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365609 eq1748164
  have eq1756029 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op (M.op x y) y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1751975 eq1368866
    | exact resolve eq1368866 eq1751975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368866
  have eq1756112 : x = (M.op (M.op (M.op x y) y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1756029
  have eq1763479 : (k x (M.op (M.op x y) y)) = (M.op x (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1756112 eq6648
    | exact resolve eq6648 eq1756112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648 eq1756112
  have eq1763553 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq206 eq1763479
    | exact resolve eq1763479 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq1763479
  have eq1763577 : (M.op x y) = (k x (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1763553
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1763553
    | exact resolve eq1763553 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763553
  have eq1776949 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1763577 eq1365359
    | exact resolve eq1365359 eq1763577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365359 eq1763577
  have eq1777135 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1776949
    | exact resolve eq1776949 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776949
  have eq1793118 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1777135 eq1751975
    | exact resolve eq1751975 eq1777135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751975 eq1777135
  have eq1793188 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1793118
  have eq1793271 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq1793188 eq55
    | exact resolve eq55 eq1793188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1793188
  have eq1793301 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq110240 eq1793271
    | exact resolve eq1793271 eq110240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110240 eq1793271
  have eq1793322 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq1793301
    | (have j0 := eq1793301 (σ x)
       grind)
    | exact resolve eq1793301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793480 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1793301 eq182
    | (have j0 := eq182 X0
       grind)
    | exact resolve eq182 eq1793301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1793301
  have eq1794061 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq110222 eq1793480
    | (have j0 := eq1793480 X0
       grind)
    | exact resolve eq1793480 eq110222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110222 eq1793480
  have eq1899175 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1794061
    | (have j0 := eq1794061 (M.op x y)
       grind)
    | exact resolve eq1794061 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794061
  have eq1899351 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1899175
  have eq1899459 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq125 eq1899351
    | exact resolve eq1899351 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1899351
  have eq1902609 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1899459 eq142
    | exact resolve eq142 eq1899459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1899459
  have eq1902931 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1365222 eq1902609
    | exact resolve eq1902609 eq1365222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365222 eq1902609
  have eq1902934 : (τ (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq112292 eq1902931
    | exact resolve eq1902931 eq112292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112292 eq1902931
  have eq1903708 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq29 eq1902934
    | exact resolve eq1902934 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902934
  have eq1903709 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq1903708
  have eq1908456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1903709 eq1793322
    | exact resolve eq1793322 eq1903709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793322 eq1903709
  have eq1908509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq1908456
  have eq1908524 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1908509
       have r₂ := eq28
       grind)
    | exact resolve eq1908509 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908509
  have eq1908673 : x ≠ (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1908524 eq203
    | exact resolve eq203 eq1908524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq1908524
  have eq1908763 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq77 x y
       grind)
    | (have r₁ := eq1908673
       have r₂ := eq77 x y
       grind)
    | exact resolve eq1908673 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1908673
  have eq1908881 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1908763
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1908763
    | exact resolve eq1908763 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908763
  have eq1913960 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1908881
       grind)
    | exact superpose eq1908881 eq45
    | exact resolve eq45 eq1908881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1914246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1913960
    | exact resolve eq1913960 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913960
  have eq1919055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1914246 eq113868
    | exact resolve eq113868 eq1914246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113868 eq1914246
  have eq1919241 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1919055
       have r₂ := eq28
       grind)
    | exact resolve eq1919055 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919055
  have eq1923011 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1908881
       have i₂ := eq1919241
       grind)
    | exact superpose eq1919241 eq1908881
    | exact resolve eq1908881 eq1919241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908881 eq1919241
  have eq1923100 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1923011
  have eq1923386 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1923100 eq29
    | exact resolve eq29 eq1923100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1923100
  have eq1924162 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1923386
    | exact resolve eq1923386 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1923386
  have eq1924163 : x = (M.op x y) := by grind
  clear eq1924162
  have eq1924198 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1924163 eq21
    | exact resolve eq21 eq1924163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1924547 : (M.op (M.op x y) y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1924163 eq107458
    | exact resolve eq107458 eq1924163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107458
  have eq1925119 : (k (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1924547
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1924547
    | exact resolve eq1924547 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924547
  have eq1925284 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1924198
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1924198
    | exact resolve eq1924198 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924198
  have eq1925411 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq1924163 eq1925119
    | exact resolve eq1925119 eq1924163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925119
  have eq1925463 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1925411
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1925411
    | exact resolve eq1925411 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1925411
  have eq1925475 : x = (k x x) := by
    first
    | exact superpose eq1924163 eq1925463
    | exact resolve eq1925463 eq1924163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924163 eq1925463
  have eq1925485 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1925284 eq27
    | exact resolve eq27 eq1925284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1925787 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1925284 eq145548
    | exact resolve eq145548 eq1925284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145548
  have eq1928736 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq575 x x
       have i₂ := eq1925475
       grind)
    | exact superpose eq1925475 eq575
    | (have j0 := eq575 x x
       grind)
    | exact resolve eq575 eq1925475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1925475
  have eq1928783 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1928736
  have eq1928784 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1928783
  have eq1928836 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1928784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1928784
    | exact resolve eq1928784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1928784
  have eq1928979 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1925284 eq1928836
    | exact resolve eq1928836 eq1925284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925284 eq1928836
  have eq1945475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1928979 eq1925787
    | exact resolve eq1925787 eq1928979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925787
  have eq1945476 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1945475
       have r₂ := eq28
       grind)
    | exact resolve eq1945475 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945475
  have eq1946546 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1945476 eq1925485
    | exact resolve eq1925485 eq1945476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925485 eq1945476
  have eq1946563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1928979 eq1946546
    | exact resolve eq1946546 eq1928979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928979 eq1946546
  have eq1946845 : False := by grind
  exact eq1946845

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
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
  have eq76 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq79 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) X1)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    grind
  have eq82 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq79 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq14 X1 X0 X0
       grind)
    | exact superpose eq14 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq45
    | (have j1 := eq99 x y
       grind)
    | exact resolve eq45 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq99 y y
       grind)
    | exact superpose eq99 eq75
    | (have j1 := eq99 y y
       grind)
    | exact resolve eq75 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq99 y sF0
       grind)
    | exact superpose eq99 eq76
    | (have j1 := eq99 y (M.op x y)
       grind)
    | exact resolve eq76 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k x (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq63
       have i₂ := eq99 sF2 sF1
       grind)
    | exact superpose eq99 eq63
    | (have j1 := eq99 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq63 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq99 sF3 sF3
       grind)
    | exact superpose eq99 eq93
    | (have j1 := eq99 (σ y) (σ y)
       grind)
    | exact resolve eq93 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq122
    | exact resolve eq122 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq142 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq149 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq162 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq99 (σ X0) sF2
       grind)
    | exact superpose eq99 eq40
    | (have j1 := eq99 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq167 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op (M.op x y) X0) X0) = (k (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op (M.op x y) X0) X0
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq214
    | exact resolve eq214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq267 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq290 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq99 (τ X0) X1
       grind)
    | exact superpose eq99 eq35
    | (have j1 := eq99 (τ X0) X1
       grind)
    | exact resolve eq35 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq347 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq413 : (k y (k (M.op x y) y)) = (τ (k (σ y) (k (σ (M.op x y)) (σ y)))) := by
    first
    | exact superpose eq149 eq267
    | exact resolve eq267 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k (σ y) X0)) ∨ y = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq99 y (τ X0)
       grind)
    | exact superpose eq99 eq267
    | (have j1 := eq99 y (τ X0)
       grind)
    | exact resolve eq267 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq433 : (k (M.op x y) (k (M.op x y) (M.op x y))) = (τ (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq167 eq290
    | exact resolve eq290 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq290
  have eq461 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X1) X3) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq55 X3 X1 X0 X2
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) X3) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X1) (M.op X3 X1)
       have r₂ := eq55 X1 X1 (M.op X3 X1) X3
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq313
    | exact resolve eq313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq313 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq313
    | (have j0 := eq313 X0 x
       grind)
    | exact resolve eq313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq313 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq313
    | (have j0 := eq313 X0 y
       grind)
    | exact resolve eq313 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq313
    | (have j0 := eq313 X0 (M.op x y)
       grind)
    | exact resolve eq313 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq550 : ∀ X0 : G, (τ (k X0 (σ y))) = (M.op (τ X0) y) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq99 (τ X0) y
       grind)
    | exact superpose eq99 eq494
    | (have j1 := eq99 (τ X0) y
       grind)
    | exact resolve eq494 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (M.op X1 X1) X0
       have j1 := eq83 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq627 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq99 (σ X0) X1
       grind)
    | exact superpose eq99 eq347
    | (have j1 := eq99 (σ X0) X1
       grind)
    | exact resolve eq347 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq123 eq99
    | (have j0 := eq99 (σ x) (σ y)
       grind)
    | exact resolve eq99 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq657
    | exact resolve eq657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq661 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq658
       have r₂ := eq28
       grind)
    | exact resolve eq658 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq669 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq661 eq13
    | exact resolve eq13 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq661 eq82
    | exact resolve eq82 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq676
    | exact resolve eq676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq1011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq679 eq123
    | exact resolve eq123 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq679
  have eq1018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1011
  have eq1021 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1018
       have r₂ := eq28
       grind)
    | exact resolve eq1018 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1027 : (τ (σ y)) = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1021 eq59
    | exact resolve eq59 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1039 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1027
    | exact resolve eq1027 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1043 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99 x y
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq99
    | (have j0 := eq99 x y
       grind)
    | exact resolve eq99 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1044 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1043
  have eq1046 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1044
    | exact resolve eq1044 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1049 : (M.op x y) = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq82 y
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq82
    | exact resolve eq82 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1055 : x ≠ y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1046
       grind)
    | exact resolve eq13 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : (M.op x y) = (k x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1049
    | exact resolve eq1049 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1134 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1058
       grind)
    | exact superpose eq1058 eq45
    | exact resolve eq45 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1140 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq1134
    | exact resolve eq1134 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq2728 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (k (σ x) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq162 eq13
    | (have j0 := eq13 (σ x) (σ X0)
       have j1 := eq162 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq162 x
       grind)
    | exact resolve eq13 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq2730 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq2728
    | (have j0 := eq2728 X0
       grind)
    | exact resolve eq2728 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2728
  have eq5245 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq310 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq310
    | exact resolve eq310 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5245 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5245
    | (have j0 := eq5245 X0 X1
       grind)
    | exact resolve eq5245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq7546 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = (k (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq461 (M.op X0 X1) X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq26983 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq112
    | exact resolve eq112 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq27052 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26983
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26983
    | exact resolve eq26983 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26983
  have eq27299 : (τ (σ x)) = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27052 eq93
    | exact resolve eq93 eq27052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27052
  have eq27328 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq27299
    | exact resolve eq27299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27299
  have eq27331 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq27328
       have r₂ := eq1055
       grind)
    | exact resolve eq27328 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq27328
  have eq27334 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq27331
       grind)
    | exact superpose eq27331 eq75
    | exact resolve eq75 eq27331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27331
  have eq27367 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27334
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27334
    | exact resolve eq27334 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27334
  have eq27401 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27367
       have i₂ := eq99 sF3 sF3
       grind)
    | exact superpose eq99 eq27367
    | (have j1 := eq99 (σ y) (σ y)
       grind)
    | exact resolve eq27367 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28853 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27401 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq27401
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq27401
       grind)
    | exact resolve eq13 eq27401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28866 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq27401
  have eq28868 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq28853
  have eq29899 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28868 eq27367
    | exact resolve eq27367 eq28868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27367 eq28868
  have eq29916 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq29899
  have eq29929 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq29916
       have r₂ := eq28866
       grind)
    | exact resolve eq29916 eq28866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28866 eq29916
  have eq29958 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29929 eq572
    | exact resolve eq572 eq29929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29929
  have eq29966 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq29958
  have eq29969 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq29966
    | exact resolve eq29966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29966
  have eq30803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29969 eq1140
    | exact resolve eq1140 eq29969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq29969
  have eq30855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq30803
  have eq30859 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq30855
       have r₂ := eq28
       grind)
    | exact resolve eq30855 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30855
  have eq30895 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq30859 eq59
    | exact resolve eq59 eq30859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30859
  have eq30935 : y = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq30 eq30895
    | exact resolve eq30895 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30895
  have eq30936 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq30935
  have eq48923 : ∀ X0 : G, (σ (τ (k X0 (σ x)))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5349 (τ X0) x
       have i₂ := eq493 X0
       grind)
    | exact superpose eq493 eq5349
    | (have j0 := eq5349 (τ X0) x
       grind)
    | exact resolve eq5349 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq48953 : ∀ X0 : G, (σ (τ (k X0 (σ (M.op x y))))) = (σ (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq495 eq5349
    | (have j0 := eq5349 (τ X0) (M.op x y)
       grind)
    | exact resolve eq5349 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq5349
  have eq49527 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq48953 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq48953
    | (have j0 := eq48953 X0
       grind)
    | exact resolve eq48953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48953
  have eq49540 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq48923 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq48923
    | (have j0 := eq48923 X0
       grind)
    | exact resolve eq48923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48923
  have eq55689 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq627 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq627
    | exact resolve eq627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq55994 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55689 X0 X1
       have i₂ := eq478 X1 X0
       grind)
    | exact superpose eq478 eq55689
    | (have j0 := eq55689 X0 X1
       grind)
    | exact resolve eq55689 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq55689
  have eq2504142 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq661 eq120
    | exact resolve eq120 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq661
  have eq2504782 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2504142
    | exact resolve eq2504142 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504142
  have eq2504785 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2504782
       grind)
    | exact superpose eq2504782 eq75
    | exact resolve eq75 eq2504782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504782
  have eq2505244 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2504785
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2504785
    | exact resolve eq2504785 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504785
  have eq2505422 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq2505244
       have r₂ := eq674
       grind)
    | exact resolve eq2505244 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq2505244
  have eq2505920 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2505422 eq93
    | exact resolve eq93 eq2505422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505422
  have eq2506315 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq2505920
    | exact resolve eq2505920 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505920
  have eq2506503 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq99 y y
       have i₂ := eq2506315
       grind)
    | exact superpose eq2506315 eq99
    | (have j0 := eq99 x y
       grind)
    | exact resolve eq99 eq2506315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2506579 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq2506503
  have eq2508166 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2506579
       grind)
    | exact superpose eq2506579 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2506579
       grind)
    | exact resolve eq13 eq2506579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2508269 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq2506579
  have eq2508276 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq2508166
  have eq2509134 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2506315
       have i₂ := eq2508276
       grind)
    | exact superpose eq2508276 eq2506315
    | exact resolve eq2506315 eq2508276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506315 eq2508276
  have eq2509330 : x = y ∨ x = (M.op y y) := by grind
  clear eq2509134
  have eq2509491 : x = (M.op y y) := by
    first
    | (have r₁ := eq2509330
       have r₂ := eq2508269
       grind)
    | exact resolve eq2509330 eq2508269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508269 eq2509330
  have eq2509770 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq112
    | exact resolve eq112 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2509793 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq669 y
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq669
    | exact resolve eq669 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq2509870 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq13
    | exact resolve eq13 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509871 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq14
    | exact resolve eq14 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509872 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 y X0 y
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq55
    | exact resolve eq55 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509890 : (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq7546 y y
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq7546
    | exact resolve eq7546 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509996 : (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2509890
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2509890
    | exact resolve eq2509890 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509890
  have eq2510018 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2509793
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2509793
    | exact resolve eq2509793 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509793
  have eq2510024 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2509770
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2509770
    | exact resolve eq2509770 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509770
  have eq2510049 : y = (k x y) := by
    first
    | (have r₁ := eq2510018
       have r₂ := eq30936
       grind)
    | exact resolve eq2510018 eq30936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30936 eq2510018
  have eq2510745 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq2510049
       grind)
    | exact superpose eq2510049 eq45
    | exact resolve eq45 eq2510049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2511110 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2510745
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2510745
    | exact resolve eq2510745 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510745
  have eq2512199 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq2510024 eq93
    | exact resolve eq93 eq2510024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2510024
  have eq2512538 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq2512199
    | exact resolve eq2512199 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512199
  have eq2512553 : x = (k y y) := by
    first
    | (have r₁ := eq2512538
       have r₂ := eq2509870
       grind)
    | exact resolve eq2512538 eq2509870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509870 eq2512538
  have eq2512558 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2512553
       grind)
    | exact superpose eq2512553 eq75
    | exact resolve eq75 eq2512553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2513006 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2512558
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2512558
    | exact resolve eq2512558 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512558
  have eq2513717 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2513006
       have i₂ := eq99 sF3 sF3
       grind)
    | exact superpose eq99 eq2513006
    | (have j1 := eq99 (σ y) (σ y)
       grind)
    | exact resolve eq2513006 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2514823 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2509871 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2509871
    | (have j0 := eq2509871 y
       grind)
    | exact resolve eq2509871 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515650 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2514823
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2514823
    | exact resolve eq2514823 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514823
  have eq2515727 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2515650 eq114
    | exact resolve eq114 eq2515650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2515743 : x ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2515650 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq2515650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515744 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2515650 eq14
    | exact resolve eq14 eq2515650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515650
  have eq2515901 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2515744 X0
       have i₂ := eq2509871 X0
       grind)
    | exact superpose eq2509871 eq2515744
    | exact resolve eq2515744 eq2509871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509871 eq2515744
  have eq2515903 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2515727
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2515727
    | exact resolve eq2515727 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515727
  have eq2520971 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2515901 eq2515903
    | exact resolve eq2515903 eq2515901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515903
  have eq2520979 : (τ (σ x)) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2520971 eq98
    | exact resolve eq98 eq2520971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq2520971
  have eq2521195 : y = (M.op (M.op x y) y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq2520979
    | exact resolve eq2520979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520979
  have eq2521305 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2513717 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq2513717
       grind)
    | exact resolve eq13 eq2513717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521409 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2513717
  have eq2521416 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2521305
  have eq2521439 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2513006 eq2521416
    | exact resolve eq2521416 eq2513006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521416
  have eq2521499 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq2521439
       have r₂ := eq2521409
       grind)
    | exact resolve eq2521439 eq2521409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521409 eq2521439
  have eq2521601 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2521499 eq14
    | exact resolve eq14 eq2521499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521602 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2521499 eq55
    | exact resolve eq55 eq2521499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521621 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2521499 eq7546
    | exact resolve eq7546 eq2521499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521719 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq2521621
    | exact resolve eq2521621 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521621
  have eq2521801 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq2521601
    | (have j0 := eq2521601 (σ y)
       grind)
    | exact resolve eq2521601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2522638 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2521499 eq2521801
    | exact resolve eq2521801 eq2521499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521801
  have eq2522751 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2522638 eq14
    | exact resolve eq14 eq2522638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522638
  have eq2522899 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2521601 eq2522751
    | exact resolve eq2522751 eq2521601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521601 eq2522751
  have eq2523062 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq2522899 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq2522899 (σ x)
       grind)
    | exact resolve eq13 eq2522899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522899
  have eq2527609 : y ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq2521195 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq2521195
       grind)
    | exact resolve eq13 eq2521195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521195
  have eq2527750 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) := by grind
  clear eq2527609
  have eq2527785 : (k y (M.op x y)) = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq2515901 eq2527750
    | exact resolve eq2527750 eq2515901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527750
  have eq2527823 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq2527785
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2527785
    | exact resolve eq2527785 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527785
  have eq2527824 : x = (k y (M.op x y)) := by grind
  clear eq2527823
  have eq2527895 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2527824 eq76
    | exact resolve eq76 eq2527824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2527824
  have eq2528248 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2527895
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2527895
    | exact resolve eq2527895 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527895
  have eq2528774 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2528248
       have i₂ := eq99 sF3 sF1
       grind)
    | exact superpose eq99 eq2528248
    | (have j1 := eq99 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq2528248 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2529729 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2528774 eq572
    | exact resolve eq572 eq2528774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq2528774
  have eq2529840 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq2529729
  have eq2529873 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2528248 eq2529840
    | exact resolve eq2529840 eq2528248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529840
  have eq2529874 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq2529873
  have eq2529973 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2528248 eq2529874
    | exact resolve eq2529874 eq2528248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528248 eq2529874
  have eq2530019 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq2529973 eq55
    | exact resolve eq55 eq2529973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529973
  have eq2530129 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2521602 eq2530019
    | exact resolve eq2530019 eq2521602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521602 eq2530019
  have eq2530134 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq2530129
    | (have j0 := eq2530129 (σ x)
       grind)
    | exact resolve eq2530129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2531296 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2530134 eq115
    | exact resolve eq115 eq2530134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2530134
  have eq2545715 : ∀ X0 : G, (τ (σ (k X0 y))) = (τ (M.op (σ X0) (σ y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq55994
    | (have j0 := eq55994 (σ X0) (σ y)
       grind)
    | exact resolve eq55994 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq55994
  have eq2548507 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2545715 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq2545715
    | (have j0 := eq2545715 X0
       grind)
    | exact resolve eq2545715 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545715
  have eq2549897 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ X0) (σ y))) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq2521499 eq2548507
    | (have j0 := eq2548507 X0
       grind)
    | exact resolve eq2548507 eq2521499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548507
  have eq2556292 : ∀ X0 : G, (τ (k X0 (σ y))) = (M.op (τ X0) y) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq550 X0
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq550
    | (have j0 := eq550 X0
       grind)
    | exact resolve eq550 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq2558361 : (M.op (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2556292
    | exact resolve eq2556292 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2558649 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149 eq2558361
    | exact resolve eq2558361 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558361
  have eq2559029 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq2558649
       have r₂ := eq2515743
       grind)
    | exact resolve eq2558649 eq2515743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515743 eq2558649
  have eq2579423 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2549897 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2549897
    | exact resolve eq2549897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2580151 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq2549897
    | (have j0 := eq2549897 (M.op x y)
       grind)
    | exact resolve eq2549897 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549897
  have eq2580810 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2559029 eq2580151
    | exact resolve eq2580151 eq2559029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580151
  have eq2581092 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op X0 (σ y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2579423 X0
       have i₂ := eq494 X0
       grind)
    | exact superpose eq494 eq2579423
    | (have j0 := eq2579423 X0
       grind)
    | exact resolve eq2579423 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq2579423
  have eq2581461 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2515901 eq49527
    | (have j0 := eq49527 X0
       grind)
    | exact resolve eq49527 eq2515901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49527
  have eq2581462 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq2515901 eq2581461
    | (have j0 := eq2581461 X0
       grind)
    | exact resolve eq2581461 eq2515901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515901 eq2581461
  have eq2581464 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2530129 eq2580810
    | exact resolve eq2580810 eq2530129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530129 eq2580810
  have eq2582084 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2581464
  have eq2583681 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 y)) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2581462 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2581462
    | exact resolve eq2581462 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581462
  have eq2584985 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (M.op X0 y)) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq2583681
    | (have j0 := eq2583681 X0
       grind)
    | exact resolve eq2583681 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2583681
  have eq2585846 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (M.op X0 (σ y)))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq2581092 eq15
    | (have j1 := eq2581092 X0
       grind)
    | exact resolve eq15 eq2581092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581092
  have eq2586781 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2585846 X0
       have i₂ := eq15 (M.op X0 sF3)
       grind)
    | exact superpose eq15 eq2585846
    | (have j0 := eq2585846 X0
       grind)
    | exact resolve eq2585846 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585846
  have eq2606780 : (τ (k (σ y) (k (σ (M.op x y)) (σ y)))) = (M.op y (k (M.op x y) y)) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | exact superpose eq149 eq418
    | exact resolve eq418 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq2607163 : (τ (k (σ y) (k (σ (M.op x y)) (σ y)))) = (M.op y (M.op (M.op x y) y)) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | exact superpose eq2559029 eq2606780
    | exact resolve eq2606780 eq2559029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606780
  have eq2607487 : (M.op y y) = (τ (k (σ y) (k (σ (M.op x y)) (σ y)))) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | exact superpose eq51 eq2607163
    | exact resolve eq2607163 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607163
  have eq2607654 : (M.op y y) = (k y (k (M.op x y) y)) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | exact superpose eq413 eq2607487
    | exact resolve eq2607487 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq2607487
  have eq2607794 : (M.op y y) = (k y (M.op (M.op x y) y)) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | exact superpose eq2559029 eq2607654
    | exact resolve eq2607654 eq2559029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607654
  have eq2607852 : x = (k y (M.op (M.op x y) y)) ∨ y = (M.op (k (M.op x y) y) (k (M.op x y) y)) := by
    first
    | (have i₁ := eq2607794
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2607794
    | exact resolve eq2607794 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607794
  have eq2607896 : y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq2559029 eq2607852
    | exact resolve eq2607852 eq2559029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607852
  have eq2607925 : y = (M.op (M.op (M.op x y) y) y) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq216 eq2607896
    | exact resolve eq2607896 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq2607896
  have eq2632994 : y ≠ y ∨ (M.op y (M.op (M.op x y) y)) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq2607925 eq13
    | (have j0 := eq13 y (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) y)
       have r₂ := eq2607925
       grind)
    | exact resolve eq13 eq2607925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607925
  have eq2633146 : (M.op y (M.op (M.op x y) y)) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by grind
  clear eq2632994
  have eq2633187 : (M.op y y) = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | exact superpose eq51 eq2633146
    | exact resolve eq2633146 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2633146
  have eq2633243 : x = (k y (M.op (M.op x y) y)) ∨ x = (k y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2633187
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2633187
    | exact resolve eq2633187 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633187
  have eq2633244 : x = (k y (M.op (M.op x y) y)) := by grind
  clear eq2633243
  have eq2714217 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2531296 eq2584985
    | (have j0 := eq2584985 x
       grind)
    | exact resolve eq2584985 eq2531296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531296 eq2584985
  have eq2714408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2714217
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq2714217
    | exact resolve eq2714217 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714217
  have eq2714578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2714408
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2714408
    | exact resolve eq2714408 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714408
  have eq2714724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq2714578
    | exact resolve eq2714578 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714578
  have eq2714844 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2714724
       have r₂ := eq28
       grind)
    | exact resolve eq2714724 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714724
  have eq2715567 : (τ (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2714844 eq2582084
    | exact resolve eq2582084 eq2714844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582084 eq2714844
  have eq2715801 : (τ (σ x)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) := by grind
  clear eq2715567
  have eq2715810 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq29 eq2715801
    | exact resolve eq2715801 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2715801
  have eq2715811 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2715810
  have eq2715862 : x ≠ (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2715811 eq213
    | exact resolve eq213 eq2715811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq2715811
  have eq2716058 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq99 x y
       grind)
    | (have r₁ := eq2715862
       have r₂ := eq99 x y
       grind)
    | exact resolve eq2715862 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq2715862
  have eq2716133 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2716058
       have i₂ := eq2510049
       grind)
    | exact superpose eq2510049 eq2716058
    | exact resolve eq2716058 eq2510049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716058
  have eq2716167 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2716133
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2716133
    | exact resolve eq2716133 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716133
  have eq2716194 : (k x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2716167 eq59
    | exact resolve eq59 eq2716167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq2716167
  have eq2717770 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq149 eq2716194
    | exact resolve eq2716194 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq2716194
  have eq2717920 : (k x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2559029 eq2717770
    | exact resolve eq2717770 eq2559029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559029 eq2717770
  have eq2717966 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2717920
       have i₂ := eq2510049
       grind)
    | exact superpose eq2510049 eq2717920
    | exact resolve eq2717920 eq2510049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717920
  have eq2724124 : (M.op (M.op y y) y) = (k (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2717966 eq7546
    | exact resolve eq7546 eq2717966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7546 eq2717966
  have eq2724282 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2724124
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2724124
    | exact resolve eq2724124 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724124
  have eq2724339 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2724282
       have i₂ := eq2510049
       grind)
    | exact superpose eq2510049 eq2724282
    | exact resolve eq2724282 eq2510049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510049 eq2724282
  have eq2724382 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2724339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2724339
    | exact resolve eq2724339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724339
  have eq2724383 : y = (M.op x y) := by grind
  clear eq2724382
  have eq2724424 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2724383 eq21
    | exact resolve eq21 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2724425 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2724383 eq46
    | exact resolve eq46 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq2724444 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2724383 eq133
    | exact resolve eq133 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq2725220 : x = (k y (M.op y y)) := by
    first
    | exact superpose eq2724383 eq2633244
    | exact resolve eq2633244 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633244
  have eq2725242 : x = (k y x) := by
    first
    | (have i₁ := eq2725220
       have i₂ := eq2509491
       grind)
    | exact superpose eq2509491 eq2725220
    | exact resolve eq2725220 eq2509491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509491 eq2725220
  have eq2725463 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2724444
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq2724444
    | exact resolve eq2724444 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2724444
  have eq2725479 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2724425
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq2724425
    | exact resolve eq2724425 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724425
  have eq2725480 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2724424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2724424
    | exact resolve eq2724424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724424
  have eq2725577 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2513006 eq2725463
    | exact resolve eq2725463 eq2513006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513006 eq2725463
  have eq2725589 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2511110 eq2725479
    | exact resolve eq2725479 eq2511110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725479
  have eq2725692 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2725480 eq27
    | exact resolve eq27 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2726576 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2725480 eq2521499
    | exact resolve eq2521499 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521499
  have eq2726578 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq2725480 eq2523062
    | (have j0 := eq2523062 X0
       grind)
    | exact resolve eq2523062 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523062
  have eq2726605 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq2725480 eq2586781
    | (have j0 := eq2586781 X0
       grind)
    | exact resolve eq2586781 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586781
  have eq2726894 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2730 y
       have i₂ := eq2725242
       grind)
    | exact superpose eq2725242 eq2730
    | (have j0 := eq2730 y
       grind)
    | exact resolve eq2730 eq2725242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2727092 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq2726894
       have r₂ := eq23
       grind)
    | exact resolve eq2726894 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726894
  have eq2727213 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2727092
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2727092
    | exact resolve eq2727092 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727092
  have eq2727334 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2727213
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq2727213
    | exact resolve eq2727213 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2727213
  have eq2727433 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2511110 eq2727334
    | exact resolve eq2727334 eq2511110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511110 eq2727334
  have eq2727510 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq2727433
    | exact resolve eq2727433 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2727433
  have eq2727573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2725480 eq2727510
    | exact resolve eq2727510 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727510
  have eq2727620 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq2727573
       have r₂ := eq28
       grind)
    | exact resolve eq2727573 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727573
  have eq2727652 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2727620
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2727620
    | exact resolve eq2727620 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727620
  have eq2727676 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2725480 eq2727652
    | exact resolve eq2727652 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727652
  have eq2727716 : (τ (k (σ (M.op x y)) (σ x))) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2725577 eq433
    | exact resolve eq433 eq2725577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq2725577
  have eq2727930 : (k y (k y y)) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq2724383 eq2727716
    | exact resolve eq2727716 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727716
  have eq2727962 : (k y (k y y)) = (k (M.op x y) x) := by
    first
    | exact superpose eq142 eq2727930
    | exact resolve eq2727930 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq2727930
  have eq2727974 : (k y (k y y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2509996 eq2727962
    | exact resolve eq2727962 eq2509996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509996 eq2727962
  have eq2727978 : (M.op y x) = (k y (k y y)) := by
    first
    | exact superpose eq2724383 eq2727974
    | exact resolve eq2727974 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727974
  have eq2727982 : (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq2727978
       have i₂ := eq2512553
       grind)
    | exact superpose eq2512553 eq2727978
    | exact resolve eq2727978 eq2512553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512553 eq2727978
  have eq2727986 : x = (M.op y x) := by
    first
    | (have i₁ := eq2727982
       have i₂ := eq2725242
       grind)
    | exact superpose eq2725242 eq2727982
    | exact resolve eq2727982 eq2725242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725242 eq2727982
  have eq2728928 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2725480 eq2725589
    | exact resolve eq2725589 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725589
  have eq2734090 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 x X0 y
       have i₂ := eq2727986
       grind)
    | exact superpose eq2727986 eq55
    | exact resolve eq55 eq2727986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727986
  have eq2734260 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2734090 X0 x
       have i₂ := eq2509872 X0 x
       grind)
    | exact superpose eq2509872 eq2734090
    | exact resolve eq2734090 eq2509872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509872 eq2734090
  have eq2735130 : ∀ X0 : G, (τ (k X0 (σ y))) = (M.op (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq2556292 X0
       have i₂ := eq2734260 (τ X0)
       grind)
    | exact superpose eq2734260 eq2556292
    | (have j0 := eq2556292 X0
       grind)
    | exact resolve eq2556292 eq2734260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2556292
  have eq2735212 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2734260 x
       grind)
    | exact superpose eq2734260 eq19
    | (have j1 := eq2734260 x
       grind)
    | exact resolve eq19 eq2734260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2734260
  have eq2735355 : y = (M.op x x) := by
    first
    | exact superpose eq2724383 eq2735212
    | exact resolve eq2735212 eq2724383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724383 eq2735212
  have eq2735408 : ∀ X0 : G, (τ (k X0 (σ (M.op x y)))) = (M.op (τ X0) x) ∨ (τ X0) = x := by
    intro X0
    first
    | exact superpose eq2725480 eq2735130
    | (have j0 := eq2735130 X0
       grind)
    | exact resolve eq2735130 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735130
  have eq2754421 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2726576 eq2726578
    | (have j0 := eq2726578 (σ (M.op x y))
       grind)
    | exact resolve eq2726578 eq2726576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726576 eq2726578
  have eq2754441 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq2726605 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq2754421
       have r₂ := eq2726605 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2754421 eq2726605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726605 eq2754421
  have eq2768914 : ∀ X0 : G, (k X0 (σ x)) = (σ (τ (k X0 (σ (M.op x y))))) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq49540 X0
       have i₂ := eq2735408 X0
       grind)
    | exact superpose eq2735408 eq49540
    | (have j0 := eq49540 X0
       have j1 := eq2735408 X0
       grind)
    | exact resolve eq49540 eq2735408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49540 eq2735408
  have eq2769195 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x x) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq2768914 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq2768914
    | (have j0 := eq2768914 X0
       grind)
    | exact resolve eq2768914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768914
  have eq2769414 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = y ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq2769195 X0
       have i₂ := eq2735355
       grind)
    | exact superpose eq2735355 eq2769195
    | (have j0 := eq2769195 X0
       grind)
    | exact resolve eq2769195 eq2735355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735355 eq2769195
  have eq2835499 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2769414 eq2521719
    | (have j1 := eq2769414 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2521719 eq2769414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521719 eq2769414
  have eq2836777 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2754441 eq2835499
    | exact resolve eq2835499 eq2754441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835499
  have eq2844873 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X1)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2836777 eq55
    | exact resolve eq55 eq2836777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836777
  have eq2845046 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2844873 x X0
       have i₂ := eq55 X0 sF1 x sF4
       grind)
    | exact superpose eq55 eq2844873
    | exact resolve eq2844873 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2844873
  have eq2855903 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2845046 eq2727676
    | exact resolve eq2727676 eq2845046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727676 eq2845046
  have eq2855945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2725692 eq2855903
    | exact resolve eq2855903 eq2725692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855903
  have eq2856231 : y = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2855945
       have r₂ := eq28
       grind)
    | exact resolve eq2855945 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855945
  have eq2857190 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2856231 eq15
    | exact resolve eq15 eq2856231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856231
  have eq2858184 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2857190
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2857190
    | exact resolve eq2857190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2857190
  have eq2858385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2725480 eq2858184
    | exact resolve eq2858184 eq2725480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725480 eq2858184
  have eq2858534 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2858385
       have r₂ := eq28
       grind)
    | exact resolve eq2858385 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858385
  have eq2858883 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2858534 eq15
    | exact resolve eq15 eq2858534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858534
  have eq2859868 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2858883
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2858883
    | exact resolve eq2858883 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2858883
  have eq2860527 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2859868 eq2754441
    | exact resolve eq2754441 eq2859868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754441 eq2859868
  have eq2860536 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2725692 eq2860527
    | exact resolve eq2860527 eq2725692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725692 eq2860527
  have eq2860598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2728928 eq2860536
    | exact resolve eq2860536 eq2728928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728928 eq2860536
  have eq2860649 : False := by grind
  exact eq2860649

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  clear eq18
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq77 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq92 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq83 (τ X0)
       grind)
    | exact superpose eq83 eq19
    | (have j1 := eq83 (τ X0)
       grind)
    | exact resolve eq19 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq83 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq102 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq96
    | (have j0 := eq96 X0
       grind)
    | exact resolve eq96 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq96
  have eq116 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (M.op (τ X1) X0) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq29
    | (have j1 := eq102 (σ X0)
       grind)
    | exact resolve eq29 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq454 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq439 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq439
    | (have j0 := eq439 X0
       grind)
    | exact resolve eq439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq467 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq454 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq454
    | (have j0 := eq454 X0
       grind)
    | exact resolve eq454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq478 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq467 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq467
    | (have j0 := eq467 X0
       grind)
    | exact resolve eq467 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq498 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq478 (σ X0)
       grind)
    | exact superpose eq478 eq29
    | (have j1 := eq478 (σ X0)
       grind)
    | exact resolve eq29 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq507 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq498
    | (have j0 := eq498 X0
       grind)
    | exact resolve eq498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq524 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq507 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq507
    | (have j0 := eq507 X0
       grind)
    | exact resolve eq507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq885 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (τ (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq524 X0
       grind)
    | exact superpose eq524 eq10
    | (have j1 := eq524 X0
       grind)
    | exact resolve eq10 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq920 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq885 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 X0
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq5093 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq5138 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5093 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5093
    | (have j0 := eq5093 X0 X1
       grind)
    | exact resolve eq5093 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5150 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq5138 X1 X0
       grind)
    | exact superpose eq5138 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq5138 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq5138 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq5138 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5138 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq5138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5138
  have eq5178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150
  have eq5201 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5178 X0 X1
       grind)
    | exact superpose eq5178 eq10
    | (have j1 := eq5178 X0 X1
       grind)
    | exact resolve eq10 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq5250 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5201 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5201
    | (have j0 := eq5201 X0 X1
       grind)
    | exact resolve eq5201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201
  have eq5251 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5272 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5251 X0 (τ X1)
       grind)
    | exact superpose eq5251 eq19
    | (have j1 := eq5251 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5275 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5251 (σ X0) (σ X1)
       grind)
    | exact superpose eq5251 eq15
    | (have j1 := eq5251 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251
  have eq5396 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5272 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5272
    | exact resolve eq5272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272
  have eq5458 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5396 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5396
    | (have j0 := eq5396 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396
  have eq5703 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5275 x y
       grind)
    | exact superpose eq5275 eq16
    | (have j1 := eq5275 x y
       grind)
    | exact resolve eq16 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq5731 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5703
       have i₂ := eq5458 y x
       grind)
    | exact superpose eq5458 eq5703
    | (have j1 := eq5458 (σ x) (σ y)
       grind)
    | (have r₁ := eq5703
       have r₂ := eq5458 y x
       grind)
    | (have r₁ := eq5703
       have r₂ := eq5458 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5703
       have r₂ := eq5458 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5703 eq5458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458 eq5703
  have eq5734 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5731
  have eq5737 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5734
       grind)
    | exact superpose eq5734 eq16
    | exact resolve eq16 eq5734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5734
  have eq5986 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq5737
       have i₂ := eq920 x
       grind)
    | exact superpose eq920 eq5737
    | (have j1 := eq920 x
       grind)
    | exact resolve eq5737 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5988 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq5989 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5988
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5988
    | exact resolve eq5988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq5991 : (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have j1 := eq478 x
       grind)
    | (have r₁ := eq5986
       have r₂ := eq478 x
       grind)
    | exact resolve eq5986 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq5986
  have eq5992 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5991
       grind)
    | exact superpose eq5991 eq16
    | exact resolve eq16 eq5991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5993 : y = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5991
       grind)
    | exact superpose eq5991 eq10
    | exact resolve eq10 eq5991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5991
  have eq6048 : x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq5993
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5993
    | exact resolve eq5993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5993
  have eq6580 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq5992
       have i₂ := eq920 x
       grind)
    | exact superpose eq920 eq5992
    | (have j1 := eq920 x
       grind)
    | exact resolve eq5992 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq5992
  have eq6583 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ x = (k x x) := by grind
  clear eq6580
  have eq6585 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq6583
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq6583
    | (have j1 := eq83 x
       grind)
    | exact resolve eq6583 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq6583
  have eq6601 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (k x x) := by
    first
    | (have j1 := eq94 x
       grind)
    | (have r₁ := eq6585
       have r₂ := eq94 x
       grind)
    | exact resolve eq6585 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq6585
  have eq6603 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq6601
       have i₂ := eq6048
       grind)
    | exact superpose eq6048 eq6601
    | exact resolve eq6601 eq6048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048 eq6601
  have eq6607 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (k x x) := by grind
  clear eq6603
  have eq6608 : x = (k x x) := by grind
  clear eq6607
  have eq337986 : (σ x) ≠ (σ x) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  have eq337987 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  clear eq337986
  have eq337992 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq337987
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq337987
    | exact resolve eq337987 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337987
  have eq337993 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq337992
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq337992
    | exact resolve eq337992 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337992
  have eq337994 : (σ x) ≠ (σ x) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5989
       have i₂ := eq337993
       grind)
    | exact superpose eq337993 eq5989
    | exact resolve eq5989 eq337993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989 eq337993
  have eq338039 : (σ x) ≠ (σ x) ∨ (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq337994
  have eq338040 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq338039
  have eq338041 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq338040
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq338040
    | exact resolve eq338040 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338040
  have eq338042 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq338041
  have eq338058 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5737
       have i₂ := eq338042
       grind)
    | exact superpose eq338042 eq5737
    | exact resolve eq5737 eq338042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737 eq338042
  have eq338151 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq338058
  have eq338187 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  have eq338188 : (σ x) = (σ y) ∨ (M.op x x) = (k x x) := by grind
  clear eq338187
  have eq338195 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq338188
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq338188
    | exact resolve eq338188 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338188
  have eq338197 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq338151
       have i₂ := eq338195
       grind)
    | exact superpose eq338195 eq338151
    | exact resolve eq338151 eq338195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338151 eq338195
  have eq338242 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq338197
  have eq338243 : (σ x) = (σ y) := by grind
  clear eq338242
  have eq338246 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq338243
       grind)
    | exact superpose eq338243 eq16
    | exact resolve eq16 eq338243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338247 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq338243
       grind)
    | exact superpose eq338243 eq10
    | exact resolve eq10 eq338243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338243
  have eq338447 : x = y := by
    first
    | (have i₁ := eq338247
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq338247
    | exact resolve eq338247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338247
  have eq338448 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq338447
       grind)
    | exact superpose eq338447 eq16
    | exact resolve eq16 eq338447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342375 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq338246
  have eq342376 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq342375
       have i₂ := eq338447
       grind)
    | exact superpose eq338447 eq342375
    | exact resolve eq342375 eq338447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338447 eq342375
  have eq342390 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq342376
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq342376
    | exact resolve eq342376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342376
  have eq342402 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq342390
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq342390
    | exact resolve eq342390 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342390
  have eq356082 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by grind
  have eq356083 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (k x x) := by grind
  clear eq356082
  have eq356091 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq356083
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq356083
    | exact resolve eq356083 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356083
  have eq356094 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq342402
       have i₂ := eq356091
       grind)
    | exact superpose eq356091 eq342402
    | exact resolve eq342402 eq356091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342402 eq356091
  have eq356139 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq356094
  have eq356140 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq356139
  have eq356167 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq338448
       have i₂ := eq356140
       grind)
    | exact superpose eq356140 eq338448
    | exact resolve eq338448 eq356140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338448 eq356140
  have eq356307 : (σ x) ≠ (σ x) ∨ (M.op x x) = (k x x) := by grind
  have eq356308 : (M.op x x) = (k x x) := by grind
  clear eq356307
  have eq356316 : x = (M.op x x) := by
    first
    | (have i₁ := eq356308
       have i₂ := eq6608
       grind)
    | exact superpose eq6608 eq356308
    | exact resolve eq356308 eq6608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608 eq356308
  have eq356320 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq356167
       have i₂ := eq356316
       grind)
    | exact superpose eq356316 eq356167
    | exact resolve eq356167 eq356316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356167 eq356316
  have eq356365 : False := by grind
  exact eq356365
