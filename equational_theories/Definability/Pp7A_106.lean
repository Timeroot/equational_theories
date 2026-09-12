import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  clear eq36
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
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
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq98
    | (have j0 := eq98 (σ X0)
       grind)
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq44
    | (have j1 := eq98 x
       grind)
    | exact resolve eq44 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq316 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq334 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq316
    | exact resolve eq316 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq339 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq334
    | exact resolve eq334 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq323 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq323 (M.op X0 X0) X0
       grind)
    | exact superpose eq323 eq323
    | exact resolve eq323 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3753 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq3771 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3773 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3753 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq3753
    | (have j0 := eq3753 X0
       grind)
    | exact resolve eq3753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753
  have eq4406 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq339 X0 X1
       grind)
    | exact superpose eq339 eq327
    | exact resolve eq327 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq339
  have eq4475 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4406 (M.op x x) (M.op x x)
       have i₂ := eq323 (M.op x x) x
       grind)
    | exact superpose eq323 eq4406
    | exact resolve eq4406 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq4406
  have eq4606 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4475 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq4475
    | exact resolve eq4475 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq4475
  have eq4666 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4606 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq4606
    | exact resolve eq4606 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq4606
  have eq21719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq21719
    | exact resolve eq21719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21719
  have eq21731 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21720
       have r₂ := eq28
       grind)
    | exact resolve eq21720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21720
  have eq21733 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq21731
    | exact resolve eq21731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21731
  have eq21758 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21733 eq14
    | exact resolve eq14 eq21733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21733
  have eq21781 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52 eq21758
    | exact resolve eq21758 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq21758
  have eq21787 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq21781
  have eq21856 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq21787
    | exact resolve eq21787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787
  have eq22858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21856 eq92
    | exact resolve eq92 eq21856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq21856
  have eq22866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq22858
  have eq22868 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22866
       have r₂ := eq28
       grind)
    | exact resolve eq22866 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22866
  have eq23150 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq22868
       grind)
    | exact superpose eq22868 eq14
    | exact resolve eq14 eq22868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22868
  have eq23173 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq23150
    | exact resolve eq23150 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq23150
  have eq23177 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq286
       have i₂ := eq23173
       grind)
    | exact superpose eq23173 eq286
    | exact resolve eq286 eq23173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23180 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq23198 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq23173
       grind)
    | exact superpose eq23173 eq12
    | exact resolve eq12 eq23173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23173
  have eq23217 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq23198
  have eq23218 : y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23217
  have eq23220 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23177
  have eq23249 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23180
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23180
    | exact resolve eq23180 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23180
  have eq23250 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23220
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23220
    | exact resolve eq23220 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23220
  have eq23960 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq23249
       grind)
    | exact superpose eq23249 eq79
    | exact resolve eq79 eq23249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23249
  have eq23978 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq23960
    | exact resolve eq23960 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23960
  have eq112742 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3773 x
       have i₂ := eq23218
       grind)
    | exact superpose eq23218 eq3773
    | (have j0 := eq3773 x
       grind)
    | exact resolve eq3773 eq23218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3773 eq23218
  have eq112807 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112742
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq112742
    | exact resolve eq112742 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq112742
  have eq112834 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112807
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq112807
    | exact resolve eq112807 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112807
  have eq112852 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112834
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112834
    | exact resolve eq112834 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112834
  have eq112863 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq112852
    | exact resolve eq112852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112852
  have eq112871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112863
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112863
    | exact resolve eq112863 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112863
  have eq189617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq112871 eq23978
    | exact resolve eq23978 eq112871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23978 eq112871
  have eq189622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq189617
  have eq189630 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq189622
       have r₂ := eq28
       grind)
    | exact resolve eq189622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189622
  have eq189994 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq190078 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq189994 eq23250
    | exact resolve eq23250 eq189994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23250 eq189994
  have eq190098 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq190078
  have eq190465 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq190098 eq189630
    | exact resolve eq189630 eq190098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189630 eq190098
  have eq190524 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq190465
  have eq190579 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq190524 eq30
    | exact resolve eq30 eq190524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq190524
  have eq190741 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq190579
    | exact resolve eq190579 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq190579
  have eq190742 : x = y := by grind
  clear eq190741
  have eq190743 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq190742
       grind)
    | exact superpose eq190742 eq19
    | exact resolve eq19 eq190742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq190744 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq190742
       grind)
    | exact superpose eq190742 eq25
    | exact resolve eq25 eq190742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq190742
  have eq191088 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq190744
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq190744
    | exact resolve eq190744 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190744
  have eq191641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq191088 eq27
    | exact resolve eq27 eq191088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq191088
  have eq191823 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq286
       have i₂ := eq190743
       grind)
    | exact superpose eq190743 eq286
    | exact resolve eq286 eq190743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq191931 : (M.op x y) = (k x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq4666 x
       have i₂ := eq190743
       grind)
    | exact superpose eq190743 eq4666
    | exact resolve eq4666 eq190743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq191967 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq191823
    | exact resolve eq191823 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191823
  have eq191986 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq217376 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191967 eq98
    | (have j0 := eq98 (σ x)
       grind)
    | exact resolve eq98 eq191967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq217387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191641 eq217376
    | exact resolve eq217376 eq191641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217376
  have eq217399 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq217387
       have r₂ := eq28
       grind)
    | exact resolve eq217387 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217387
  have eq217404 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191641 eq217399
    | exact resolve eq217399 eq191641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217399
  have eq217435 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217404 eq191986
    | exact resolve eq191986 eq217404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191986 eq217404
  have eq217449 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191641 eq217435
    | exact resolve eq217435 eq191641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217435
  have eq218113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217449 eq191967
    | exact resolve eq191967 eq217449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191967 eq217449
  have eq218124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq218113
  have eq218129 : x = (M.op x y) := by
    first
    | (have r₁ := eq218124
       have r₂ := eq28
       grind)
    | exact resolve eq218124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218124
  have eq218137 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq218129 eq21
    | exact resolve eq21 eq218129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq218775 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq218129 eq191931
    | exact resolve eq191931 eq218129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191931
  have eq218781 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq218775
       have i₂ := eq190743
       grind)
    | exact superpose eq190743 eq218775
    | exact resolve eq218775 eq190743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190743 eq218775
  have eq218951 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq218137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq218137
    | exact resolve eq218137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218137
  have eq218954 : x = (k x x) := by
    first
    | exact superpose eq218129 eq218781
    | exact resolve eq218781 eq218129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218129 eq218781
  have eq220712 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3771 x
       have i₂ := eq218954
       grind)
    | exact superpose eq218954 eq3771
    | (have j0 := eq3771 x
       grind)
    | exact resolve eq3771 eq218954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771 eq218954
  have eq220715 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq220712
  have eq220725 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq220715
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq220715
    | exact resolve eq220715 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq220715
  have eq220747 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191641 eq220725
    | exact resolve eq220725 eq191641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191641 eq220725
  have eq220767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218951 eq220747
    | exact resolve eq220747 eq218951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218951 eq220747
  have eq220785 : False := by grind
  exact eq220785

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyy_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X0 X1
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq53 X1 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq23 (M.op X1 X1) X0
       grind)
    | exact superpose eq23 eq97
    | exact resolve eq97 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq23 X1 X1
       grind)
    | exact superpose eq23 eq99
    | exact resolve eq99 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq67
    | (have j0 := eq67 (σ X0) (σ X1)
       grind)
    | exact resolve eq67 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq67 X0 (τ X1)
       grind)
    | exact superpose eq67 eq18
    | (have j1 := eq67 X0 (τ X1)
       grind)
    | exact resolve eq18 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq67
  have eq231 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq232 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq231 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq254 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq232 (τ X0)
       grind)
    | exact superpose eq232 eq17
    | exact resolve eq17 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq255 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq254 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq254
    | exact resolve eq254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq255 X0
       have i₂ := eq232 X0
       grind)
    | exact superpose eq232 eq255
    | exact resolve eq255 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq255
  have eq278 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq268 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq268
    | exact resolve eq268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq440 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0) (σ X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq23
    | exact resolve eq23 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq9
    | exact resolve eq9 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq278 (M.op X0 X0)
       grind)
    | exact superpose eq278 eq443
    | exact resolve eq443 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq449 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq440 X0
       have i₂ := eq278 (M.op X0 X0)
       grind)
    | exact superpose eq278 eq440
    | exact resolve eq440 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq451 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq447 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq447
    | exact resolve eq447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq452 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq449 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq449
    | exact resolve eq449 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq449
  have eq455 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq187
    | exact resolve eq187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq455
    | (have j0 := eq455 X0 X1
       grind)
    | exact resolve eq455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq899 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq945 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 X1
       have i₂ := eq94 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq94 eq899
    | exact resolve eq899 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq899
  have eq2148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq278
  have eq2172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2148 x y
       grind)
    | exact superpose eq2148 eq16
    | (have j1 := eq2148 x y
       grind)
    | exact resolve eq16 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq6087 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq2172
       have i₂ := eq452 x
       grind)
    | exact superpose eq452 eq2172
    | exact resolve eq2172 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq2172
  have eq6093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x (M.op x x))) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq6087
       have i₂ := eq489 y x
       grind)
    | exact superpose eq489 eq6087
    | (have j1 := eq489 y x
       grind)
    | (have r₁ := eq6087
       have r₂ := eq489 y x
       grind)
    | exact resolve eq6087 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq6087
  have eq6096 : (σ y) = (σ (M.op x (M.op x x))) ∨ y = (M.op x (M.op x x)) := by grind
  clear eq6093
  have eq135541 : (M.op x (M.op x x)) = (τ (σ y)) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq10 (M.op x (M.op x x))
       have i₂ := eq6096
       grind)
    | exact superpose eq6096 eq10
    | exact resolve eq10 eq6096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6096
  have eq135707 : y = (M.op x (M.op x x)) ∨ y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq135541
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq135541
    | exact resolve eq135541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135541
  have eq135708 : y = (M.op x (M.op x x)) := by grind
  clear eq135707
  have eq135796 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq451 x
       have i₂ := eq135708
       grind)
    | exact superpose eq135708 eq451
    | exact resolve eq451 eq135708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq135835 : x = (M.op x y) := by
    first
    | (have i₁ := eq945 x x
       have i₂ := eq135708
       grind)
    | exact superpose eq135708 eq945
    | exact resolve eq945 eq135708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq135708
  have eq175352 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135796
       grind)
    | exact superpose eq135796 eq16
    | exact resolve eq16 eq135796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135796
  have eq175571 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq175352
       have i₂ := eq135835
       grind)
    | exact superpose eq135835 eq175352
    | exact resolve eq175352 eq135835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135835 eq175352
  have eq175572 : False := by grind
  exact eq175572

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, X0 = X1 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq53 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq53 X0 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq23 (M.op X1 X1) X0
       grind)
    | exact superpose eq23 eq97
    | exact resolve eq97 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq23 X1 X1
       grind)
    | exact superpose eq23 eq99
    | exact resolve eq99 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq122 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq64
    | (have j0 := eq64 (k (M.op X1 (M.op X0 X0)) X1) X0
       grind)
    | exact resolve eq64 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq148 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) (M.op X0 X0))) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (τ X1) (M.op X0 X0))
       have i₂ := eq122 X0 (τ X1)
       grind)
    | exact superpose eq122 eq18
    | (have j1 := eq122 (σ X0) (k (σ (M.op (τ X1) (M.op X0 X0))) X1)
       grind)
    | exact resolve eq18 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq122
  have eq177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq67
    | (have j0 := eq67 (σ X1) (σ X0)
       grind)
    | exact resolve eq67 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq230 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq231 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq250 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq231 (σ X0)
       grind)
    | exact superpose eq231 eq29
    | exact resolve eq29 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq251 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq231 (τ X0)
       grind)
    | exact superpose eq231 eq32
    | exact resolve eq32 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq253 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq231 (τ X0)
       grind)
    | exact superpose eq231 eq17
    | exact resolve eq17 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq254 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq253 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253
    | exact resolve eq253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq231 X0
       grind)
    | exact superpose eq231 eq251
    | exact resolve eq251 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq257 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq250 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq267 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq254 X0
       have i₂ := eq231 X0
       grind)
    | exact superpose eq231 eq254
    | exact resolve eq254 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq257 X0
       have i₂ := eq231 X0
       grind)
    | exact superpose eq231 eq257
    | exact resolve eq257 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq257
  have eq277 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq267 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq267
    | exact resolve eq267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ X0) (τ X0)
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq9
    | exact resolve eq9 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq356 X0
       have i₂ := eq256 (M.op X0 X0)
       grind)
    | exact superpose eq256 eq356
    | exact resolve eq356 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq363 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq359
    | exact resolve eq359 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq366 : ∀ X0 X1 : G, (σ X1) = (k (σ (M.op X0 (M.op X1 X1))) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq408 : ∀ X0 X1 : G, (σ X1) = (σ (k (M.op X0 (M.op X1 X1)) X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq15 (M.op X0 (M.op X1 X1)) X0
       grind)
    | exact superpose eq15 eq366
    | (have j0 := eq366 (σ X1) (σ (k (M.op X0 (M.op X1 X1)) X0))
       grind)
    | exact resolve eq366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq432 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ X0) (σ X0)
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq23
    | exact resolve eq23 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq277 (M.op X0 X0)
       grind)
    | exact superpose eq277 eq432
    | exact resolve eq432 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq444 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq441
    | exact resolve eq441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq488 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (σ X0)
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq94
    | exact resolve eq94 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (τ X0)
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq94
    | exact resolve eq94 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq501 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (M.op X2 (σ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq488 (M.op X0 X1) X2
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq488
    | exact resolve eq488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq363 (σ (M.op X0 X0))
       have i₂ := eq488 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq488 eq363
    | exact resolve eq363 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq617 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq604 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq604
    | exact resolve eq604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq624 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq617
    | exact resolve eq617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq756 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0) (σ X0)
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq103
    | exact resolve eq103 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq794 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq488 X0 (σ X0)
       grind)
    | exact superpose eq488 eq764
    | exact resolve eq764 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq764
  have eq799 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq94 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq94 eq756
    | exact resolve eq756 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1914 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq277 X1
       grind)
    | exact superpose eq277 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq277
  have eq2037 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1914 y x
       grind)
    | exact superpose eq1914 eq16
    | (have j1 := eq1914 y x
       grind)
    | exact resolve eq16 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq2161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq408 X1 (M.op X1 X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq408
    | (have j0 := eq408 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq408 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq4911 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq2037
       have i₂ := eq444 x
       grind)
    | exact superpose eq444 eq2037
    | exact resolve eq2037 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq2037
  have eq4918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4911
       have i₂ := eq2161 y x
       grind)
    | exact superpose eq2161 eq4911
    | (have j1 := eq2161 y x
       grind)
    | (have r₁ := eq4911
       have r₂ := eq2161 y x
       grind)
    | exact resolve eq4911 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq4911
  have eq4919 : x = (M.op x y) ∨ (σ y) = (σ (M.op x (M.op x x))) := by grind
  clear eq4918
  have eq9150 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) = (M.op X1 (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq501 (τ (M.op X0 X0)) (τ (M.op X0 X0)) X1
       have i₂ := eq489 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq489 eq501
    | exact resolve eq501 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq501
  have eq9260 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9150 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9150
    | exact resolve eq9150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9150
  have eq9298 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9260 X0 X1
       have i₂ := eq267 (M.op X0 X0)
       grind)
    | exact superpose eq267 eq9260
    | exact resolve eq9260 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq9260
  have eq9330 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9298 X0 X1
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq9298
    | exact resolve eq9298 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9298
  have eq9577 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9330 X1 X2
       have i₂ := eq9330 X1 X0
       grind)
    | (have i₁ := eq9330 X0 X1
       have i₂ := eq9330 X0 X0
       grind)
    | exact superpose eq9330 eq9330
    | exact resolve eq9330 eq9330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9330
  have eq10162 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9577 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq799 X0 X1
       grind)
    | exact superpose eq799 eq9577
    | exact resolve eq9577 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq9577
  have eq19766 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ y) = (σ (M.op x (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq10162 y x X0
       have i₂ := eq4919
       grind)
    | exact superpose eq4919 eq10162
    | exact resolve eq10162 eq4919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4919 eq10162
  have eq20171 : (σ y) = (σ (M.op x (M.op x x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19766 x
       have i₂ := eq94 x x
       grind)
    | exact superpose eq94 eq19766
    | exact resolve eq19766 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq19766
  have eq94541 : (M.op (M.op x (M.op x x)) (M.op x (M.op x x))) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq269 (M.op x (M.op x x))
       have i₂ := eq20171
       grind)
    | exact superpose eq20171 eq269
    | exact resolve eq269 eq20171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20171
  have eq94662 : (M.op y y) = (M.op (M.op x (M.op x x)) (M.op x (M.op x x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94541
       have i₂ := eq269 y
       grind)
    | exact superpose eq269 eq94541
    | exact resolve eq94541 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq94541
  have eq94706 : (M.op y y) = (M.op x (M.op (M.op x x) (M.op x x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94662
       have i₂ := eq23 (M.op x x) x
       grind)
    | exact superpose eq23 eq94662
    | exact resolve eq94662 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq94662
  have eq94718 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94706
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq94706
    | exact resolve eq94706 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94706
  have eq94719 : x = (M.op y y) := by grind
  clear eq94718
  have eq95190 : x = (M.op x y) := by
    first
    | (have i₁ := eq624 y
       have i₂ := eq94719
       grind)
    | exact superpose eq94719 eq624
    | exact resolve eq624 eq94719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq95195 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq794 y
       have i₂ := eq94719
       grind)
    | exact superpose eq94719 eq794
    | exact resolve eq794 eq94719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq94719
  have eq110667 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95195
       grind)
    | exact superpose eq95195 eq16
    | exact resolve eq16 eq95195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95195
  have eq110847 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq110667
       have i₂ := eq95190
       grind)
    | exact superpose eq95190 eq110667
    | exact resolve eq110667 eq95190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95190 eq110667
  have eq110848 : False := by grind
  exact eq110848

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  clear eq19
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq55 (τ X0) X1
       grind)
    | exact superpose eq55 eq18
    | (have j1 := eq55 (τ X0) X1
       grind)
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq77
    | exact resolve eq77 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq81 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq75
    | exact resolve eq75 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq84 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq81
    | exact resolve eq81 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq108 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | (have j1 := eq66 X0 X1
       grind)
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq108
    | (have j1 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq108 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq108
  have eq335 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq332
  have eq343 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq76 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq76 (M.op X0 X0) X0
       grind)
    | exact superpose eq76 eq76
    | exact resolve eq76 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (M.op (τ X1) (M.op X0 X0)))) ∨ (τ X1) = (M.op (M.op (τ X1) (M.op X0 X0)) (M.op (τ X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op (τ X1) (M.op X0 X0))
       have i₂ := eq76 (τ X1) X0
       grind)
    | exact superpose eq76 eq72
    | (have j0 := eq72 X1 (M.op (τ X1) (M.op X0 X0))
       grind)
    | exact resolve eq72 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq347 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (k X1 (σ (M.op (τ X1) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq24 (M.op X0 X0) (τ X1)
       grind)
    | exact superpose eq24 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq348 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (M.op X0 X0))) ∨ (σ X0) = (k X1 (σ (M.op (τ X1) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq347
    | (have j0 := eq347 X0 X1
       grind)
    | exact resolve eq347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq353 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq41 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq41 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq355 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq953 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (M.op (M.op (σ (k X1 X0)) (σ (k X1 X0))) (M.op (σ (k X1 X0)) (σ (k X1 X0))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op (σ (k X0 X1)) (σ (k X0 X1))) (σ X0)
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq24
    | (have j1 := eq110 X1 X0
       grind)
    | exact resolve eq24 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq955 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (M.op (σ (k X1 X0)) (M.op (σ (k X1 X0)) (σ (k X1 X0))))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq24 (σ (k X1 X0)) (σ (k X1 X0))
       grind)
    | exact superpose eq24 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq5628 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))))) ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (τ X1) (M.op X0 (M.op X0 X0))
       have i₂ := eq348 X0 X1
       grind)
    | exact superpose eq348 eq83
    | (have j1 := eq348 X1 X0
       grind)
    | exact resolve eq83 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq348
  have eq5650 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1)))))) ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5628 X0 X1
       have i₂ := eq24 (M.op X1 X1) X1
       grind)
    | exact superpose eq24 eq5628
    | (have j0 := eq5628 X0 X1
       grind)
    | exact resolve eq5628 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5628
  have eq5676 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))))) ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5650 X0 X1
       have i₂ := eq84 X1 (M.op X1 X1)
       grind)
    | exact superpose eq84 eq5650
    | (have j0 := eq5650 X0 X1
       grind)
    | exact resolve eq5650 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq5650
  have eq5689 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (M.op X1 X1))) ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5676 X0 X1
       have i₂ := eq76 (M.op X1 X1) X1
       grind)
    | exact superpose eq76 eq5676
    | (have j0 := eq5676 X0 X1
       grind)
    | exact resolve eq5676 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5676
  have eq5698 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 X1)))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5689 X0 X1
       have i₂ := eq76 (τ X0) X1
       grind)
    | exact superpose eq76 eq5689
    | (have j0 := eq5689 X0 X1
       grind)
    | exact resolve eq5689 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq6455 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq355 (σ X0) X1
       grind)
    | exact superpose eq355 eq23
    | (have j1 := eq355 (σ X0) X1
       grind)
    | exact resolve eq23 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq355
  have eq6471 : ∀ X0 X1 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6455 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq6455
    | (have j0 := eq6455 X0 X1
       grind)
    | exact resolve eq6455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6455
  have eq6489 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6471 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6471
    | (have j0 := eq6471 X0 X1
       grind)
    | exact resolve eq6471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6471
  have eq6500 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6489 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6489
    | (have j0 := eq6489 X0 X1
       grind)
    | exact resolve eq6489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6489
  have eq87827 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (τ (σ X1)) (M.op X0 X0))))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (σ (M.op (τ (σ X1)) (M.op X0 X0)))
       have i₂ := eq5698 (σ X1) X0
       grind)
    | exact superpose eq5698 eq30
    | (have j1 := eq5698 (σ X0) (k X1 (τ (σ (M.op (τ (σ X1)) (M.op X0 X0)))))
       grind)
    | exact resolve eq30 eq5698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5698
  have eq87985 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op (τ (σ X1)) (M.op X0 X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87827 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq87827
    | (have j0 := eq87827 (k X1 (M.op (τ (σ X1)) (M.op X0 X0))) X0
       grind)
    | exact resolve eq87827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87827
  have eq88079 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op X1 (M.op X0 X0))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87985 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq87985
    | (have j0 := eq87985 (k X1 (M.op X1 (M.op X0 X0))) X0
       grind)
    | exact resolve eq87985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87985
  have eq88148 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op X0 X0))) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq88079 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88079
    | (have j0 := eq88079 X0 X1
       grind)
    | exact resolve eq88079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88079
  have eq88153 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op X0 X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88148 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq88148
    | (have j0 := eq88148 X0 X1
       grind)
    | exact resolve eq88148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88148
  have eq88794 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88153 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq88153
    | (have j0 := eq88153 (M.op X1 X0) (k X1 X0)
       grind)
    | exact resolve eq88153 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88153
  have eq90090 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6500 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500
  have eq90093 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq90090 X0
       have j1 := eq88794 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq90090 X0
       have r₂ := eq88794 X0 (M.op X0 X0)
       grind)
    | exact resolve eq90090 eq88794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88794 eq90090
  have eq90187 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq90093 X0
       have i₂ := eq343 X0
       grind)
    | exact superpose eq343 eq90093
    | exact resolve eq90093 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90093
  have eq90262 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq90187 y
       have i₂ := eq335
       grind)
    | exact superpose eq335 eq90187
    | exact resolve eq90187 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq90291 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq955 X0 (M.op X0 X0)
       have i₂ := eq90187 X0
       grind)
    | exact superpose eq90187 eq955
    | (have j0 := eq955 X0 (M.op X0 X0)
       grind)
    | exact resolve eq955 eq90187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90187
  have eq90460 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90291 X0
       have i₂ := eq76 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       grind)
    | exact superpose eq76 eq90291
    | (have j0 := eq90291 X0
       grind)
    | exact resolve eq90291 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90291
  have eq90461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq90460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90460
  have eq92755 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq343 (σ X0)
       have i₂ := eq90461 X0
       grind)
    | exact superpose eq90461 eq343
    | exact resolve eq343 eq90461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133995 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90262
       have i₂ := eq90461 y
       grind)
    | exact superpose eq90461 eq90262
    | exact resolve eq90262 eq90461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90262
  have eq134018 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq955 y x
       have i₂ := eq133995
       grind)
    | exact superpose eq133995 eq955
    | (have j0 := eq955 y x
       grind)
    | exact resolve eq955 eq133995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq133995
  have eq134059 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq134018
       have i₂ := eq76 (σ x) (σ x)
       grind)
    | exact superpose eq76 eq134018
    | exact resolve eq134018 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq134018
  have eq134060 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq134059
  have eq134096 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq134060
       have i₂ := eq90461 y
       grind)
    | exact superpose eq90461 eq134060
    | exact resolve eq134060 eq90461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90461 eq134060
  have eq134097 : (σ x) = (σ (M.op y y)) := by grind
  clear eq134096
  have eq135138 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92755 y
       have i₂ := eq134097
       grind)
    | exact superpose eq134097 eq92755
    | exact resolve eq92755 eq134097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92755
  have eq135145 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq134097
       grind)
    | exact superpose eq134097 eq10
    | exact resolve eq10 eq134097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134097
  have eq135647 : x = (M.op y y) := by
    first
    | (have i₁ := eq135145
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq135145
    | exact resolve eq135145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135145
  have eq136533 : x = (M.op x y) := by
    first
    | (have i₁ := eq343 y
       have i₂ := eq135647
       grind)
    | exact superpose eq135647 eq343
    | exact resolve eq343 eq135647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq135647
  have eq162489 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq135138
       grind)
    | exact superpose eq135138 eq16
    | exact resolve eq16 eq135138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135138
  have eq162648 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq162489
       have i₂ := eq136533
       grind)
    | exact superpose eq136533 eq162489
    | exact resolve eq162489 eq136533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136533 eq162489
  have eq162649 : False := by grind
  exact eq162649

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_x_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq63
    | exact resolve eq63 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq16
    | (have j1 := eq110 y x
       grind)
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq297 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq97
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq301 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq297 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq297
    | exact resolve eq297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq119
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq718 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq717
  have eq745 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66
  have eq3201 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq301
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3390 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 (σ X0)))) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3201 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3201
    | exact resolve eq3201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq6288 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 X1)) = (τ (τ (M.op X0 (M.op X0 (σ (σ X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3390 X1 x X3
       have i₂ := eq3390 (σ X1) X0 x
       grind)
    | exact superpose eq3390 eq3390
    | exact resolve eq3390 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6325 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3390 (σ (M.op X0 X0)) X1 (σ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq3390
    | exact resolve eq3390 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3390
  have eq6509 : ∀ X0 X1 : G, (σ X0) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6325 X0 X1
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq6325
    | exact resolve eq6325 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq6325
  have eq7752 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718
       grind)
    | exact superpose eq718 eq16
    | exact resolve eq16 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq7753 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7752
       have r₂ := eq22 x
       grind)
    | exact resolve eq7752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752
  have eq304447 : ∀ X0 : G, (σ y) = (τ (M.op X0 (M.op X0 (σ (σ (M.op x x)))))) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6509 y X0
       have i₂ := eq7753
       grind)
    | exact superpose eq7753 eq6509
    | exact resolve eq6509 eq7753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753
  have eq304599 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq304447 x
       have i₂ := eq6509 x x
       grind)
    | exact superpose eq6509 eq304447
    | exact resolve eq304447 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304447
  have eq304600 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq304599
  have eq304631 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq304600
       grind)
    | exact superpose eq304600 eq22
    | exact resolve eq22 eq304600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304600
  have eq305031 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq304631
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq304631
    | exact resolve eq304631 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304631
  have eq305032 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq305031
  have eq305440 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (τ (M.op X1 (M.op X1 (σ (σ (M.op x x))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6288 X1 (M.op y y) X0
       have i₂ := eq305032
       grind)
    | exact superpose eq305032 eq6288
    | exact resolve eq6288 eq305032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288 eq305032
  have eq305495 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq305440 X0 x
       have i₂ := eq6509 x x
       grind)
    | exact superpose eq6509 eq305440
    | exact resolve eq305440 eq6509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509 eq305440
  have eq305735 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq305495 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq305495
    | exact resolve eq305495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305495
  have eq305774 : x = y := by
    first
    | (have i₁ := eq305735 x
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq305735
    | exact resolve eq305735 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq305735
  have eq305785 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq305774
       grind)
    | exact superpose eq305774 eq16
    | exact resolve eq16 eq305774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305774
  have eq305786 : False := by grind
  exact eq305786

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq64
    | exact resolve eq64 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq74 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq40
  have eq92 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq81
    | (have j0 := eq81 X0
       grind)
    | exact resolve eq81 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq95
    | (have j0 := eq95 X0
       grind)
    | exact resolve eq95 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq122 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113 y x
       grind)
    | exact superpose eq113 eq16
    | (have j1 := eq113 y x
       grind)
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq9
    | (have j1 := eq113 X0 X1
       grind)
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq125 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (M.op (k X0 X1) (k X0 X1)))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq23 (k X0 X1)
       grind)
    | exact superpose eq23 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq301 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq102
    | exact resolve eq102 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq309 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq301 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq301 eq102
    | exact resolve eq102 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq301
  have eq408 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq309 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq309
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq416 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq408 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq408
    | exact resolve eq408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq419 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq416 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq416
    | exact resolve eq416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq466 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq419 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq419
    | exact resolve eq419 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq122
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq122
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq122
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq122
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq122 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq617 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq616
  have eq716 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq67
    | exact resolve eq67 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (M.op (σ (M.op (k X0 X1) (k X0 X1))) (σ (M.op (k X0 X1) (k X0 X1))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ (M.op (k X0 X1) (k X0 X1))) (σ X1)
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq25
    | (have j1 := eq125 X0 X1
       grind)
    | exact resolve eq25 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ (M.op (M.op (k X0 X1) (k X0 X1)) (M.op (k X0 X1) (k X0 X1))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2196 X0 X1
       have i₂ := eq23 (M.op (k X0 X1) (k X0 X1))
       grind)
    | exact superpose eq23 eq2196
    | (have j0 := eq2196 X0 X1
       grind)
    | exact resolve eq2196 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq2220 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ (M.op (k X0 X1) (M.op (k X0 X1) (k X0 X1))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2199 X0 X1
       have i₂ := eq25 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq25 eq2199
    | (have j0 := eq2199 X0 X1
       grind)
    | exact resolve eq2199 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2199
  have eq2235 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ (M.op (k X0 X1) (M.op (k X0 X1) (k X0 X1))))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2220 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq2220
    | (have j0 := eq2220 X0 X1
       grind)
    | exact resolve eq2220 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq6448 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq16
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq6449 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6448
       have r₂ := eq23 x
       grind)
    | exact resolve eq6448 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq227780 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq97 y
       have i₂ := eq6449
       grind)
    | exact superpose eq6449 eq97
    | exact resolve eq97 eq6449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq6449
  have eq227992 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq227780
  have eq2758838 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2235 y x
       have i₂ := eq227992
       grind)
    | exact superpose eq227992 eq2235
    | (have j0 := eq2235 y x
       grind)
    | exact resolve eq2235 eq227992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235 eq227992
  have eq2758985 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op x (M.op x x)))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq2758838
  have eq2759015 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2758985
       have i₂ := eq716 x
       grind)
    | exact superpose eq716 eq2758985
    | exact resolve eq2758985 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq2758985
  have eq2759016 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2759015
  have eq2763096 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2759016
       grind)
    | exact superpose eq2759016 eq10
    | exact resolve eq10 eq2759016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759016
  have eq2764199 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2763096
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2763096
    | exact resolve eq2763096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763096
  have eq2768300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2764199
       grind)
    | exact superpose eq2764199 eq16
    | exact resolve eq16 eq2764199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764199
  have eq2768301 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2768300
       have r₂ := eq23 x
       grind)
    | exact resolve eq2768300 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2768300
  have eq2768335 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq466 y
       have i₂ := eq2768301
       grind)
    | exact superpose eq2768301 eq466
    | exact resolve eq466 eq2768301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq2768471 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2768301
       grind)
    | exact superpose eq2768301 eq10
    | exact resolve eq10 eq2768301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768301
  have eq2769847 : x = (M.op y y) := by
    first
    | (have i₁ := eq2768471
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2768471
    | exact resolve eq2768471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768471
  have eq2770034 : x = (M.op x y) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq2769847
       grind)
    | exact superpose eq2769847 eq419
    | exact resolve eq419 eq2769847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq2769847
  have eq2994190 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2768335
       grind)
    | exact superpose eq2768335 eq16
    | exact resolve eq16 eq2768335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768335
  have eq2994752 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2994190
       have i₂ := eq2770034
       grind)
    | exact superpose eq2770034 eq2994190
    | exact resolve eq2994190 eq2770034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770034 eq2994190
  have eq2994753 : False := by grind
  exact eq2994753

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq10160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10160
    | exact resolve eq10160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10167 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10161
       have r₂ := eq28
       grind)
    | exact resolve eq10161 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10161
  have eq10169 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10167
    | exact resolve eq10167 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10167
  have eq10172 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10169 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10169
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10169
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10169
       grind)
    | exact resolve eq12 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10169
  have eq10184 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq10172
  have eq10186 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10184
       have r₂ := eq27
       grind)
    | exact resolve eq10184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10184
  have eq10191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10186 eq115
    | exact resolve eq115 eq10186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq10186
  have eq10198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10191
  have eq10201 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10198
       have r₂ := eq28
       grind)
    | exact resolve eq10198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq10315 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10201
       grind)
    | exact superpose eq10201 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10201
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10201
       grind)
    | exact resolve eq12 eq10201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10327 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10315
  have eq10329 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10327
       have r₂ := eq19
       grind)
    | exact resolve eq10327 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10327
  have eq10333 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq10329
       grind)
    | exact superpose eq10329 eq88
    | exact resolve eq88 eq10329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq10329
  have eq10349 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10333
    | exact resolve eq10333 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10333
  have eq10489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10349 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10489
  have eq10494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq10490
    | exact resolve eq10490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10490
  have eq10500 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10494
       have r₂ := eq28
       grind)
    | exact resolve eq10494 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10494
  have eq10502 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq10500
    | exact resolve eq10500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10500
  have eq10634 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10502 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10502
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10502
       grind)
    | exact resolve eq12 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10646 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq10634
  have eq10648 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10646
       have r₂ := eq27
       grind)
    | exact resolve eq10646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq10659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10648 eq10349
    | exact resolve eq10349 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10349 eq10648
  have eq10662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10659
  have eq10667 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10662
       have r₂ := eq28
       grind)
    | exact resolve eq10662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10662
  have eq10783 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10667 eq30
    | exact resolve eq30 eq10667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10667
  have eq10845 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10783
    | exact resolve eq10783 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10783
  have eq10846 : x = y := by grind
  clear eq10845
  have eq10856 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10846
       grind)
    | exact superpose eq10846 eq19
    | exact resolve eq19 eq10846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10857 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10846
       grind)
    | exact superpose eq10846 eq25
    | exact resolve eq25 eq10846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10846
  have eq10963 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10857
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10857
    | exact resolve eq10857 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10857
  have eq10978 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10963 eq27
    | exact resolve eq27 eq10963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10963
  have eq11358 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10978 eq76
    | exact resolve eq76 eq10978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10978
  have eq11387 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11358
       have i₂ := eq10856
       grind)
    | exact superpose eq10856 eq11358
    | exact resolve eq11358 eq10856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10856 eq11358
  have eq11392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11387 eq15
    | exact resolve eq15 eq11387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11392
    | exact resolve eq11392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq11392
  have eq11442 : False := by grind
  exact eq11442

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_x_pxy_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq48 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
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
  have eq58 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
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
  have eq84 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
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
  clear eq41
  have eq105 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  have eq113 : (k x y) = (τ (k (σ x) (σ y))) := by
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
  have eq147 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq58 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58
    | (have j0 := eq58 y
       grind)
    | exact resolve eq58 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq156 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq69 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq69
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq168 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq84 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq84
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq202 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op X1 (M.op (k X0 X1) (k X0 X1))) = X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq11 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = y := by
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
  have eq211 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq213 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X0) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq204 X1 X0
       grind)
    | exact superpose eq204 eq209
    | (have j0 := eq209 X0 X1
       grind)
    | exact resolve eq209 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X0) ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq213 X1 X0
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq213
    | (have j0 := eq213 X0 X1
       grind)
    | exact resolve eq213 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq217 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X0) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq204 X1 X0
       grind)
    | exact superpose eq204 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq221 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq202 eq16
    | exact resolve eq16 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq203 eq16
    | exact resolve eq16 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq16 (M.op y y) x
       have i₂ := eq221
       grind)
    | exact superpose eq221 eq16
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq227
       have i₂ := eq204 sF0 sF0
       grind)
    | exact superpose eq204 eq227
    | exact resolve eq227 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq231 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq224 eq16
    | exact resolve eq16 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq231
       have i₂ := eq204 sF4 sF4
       grind)
    | exact superpose eq204 eq231
    | exact resolve eq231 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq582 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq204
    | exact resolve eq204 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq204
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq204
    | exact resolve eq204 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq228 eq204
    | exact resolve eq204 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq591 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq232 eq204
    | exact resolve eq204 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq593 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq204 X1 X0
       grind)
    | exact superpose eq204 eq16
    | exact resolve eq16 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq16
    | exact resolve eq16 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq204 (M.op X1 X1) X0
       grind)
    | exact superpose eq204 eq594
    | exact resolve eq594 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq597 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq591
       have i₂ := eq204 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq204 eq591
    | exact resolve eq591 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq600 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq204 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq204 eq587
    | exact resolve eq587 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq602 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq204 (M.op X1 X1) X0
       grind)
    | exact superpose eq204 eq584
    | exact resolve eq584 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq603 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq204 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq204 eq582
    | exact resolve eq582 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq604 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq204 X1 X1
       grind)
    | exact superpose eq204 eq595
    | exact resolve eq595 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq606 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq597
       have i₂ := eq16 sF4 sF4
       grind)
    | exact superpose eq16 eq597
    | exact resolve eq597 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq608 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq600
       have i₂ := eq16 sF0 sF0
       grind)
    | exact superpose eq16 eq600
    | exact resolve eq600 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq204 X1 X1
       grind)
    | exact superpose eq204 eq602
    | exact resolve eq602 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq610 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq603
    | exact resolve eq603 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq611 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq606
       have i₂ := eq204 sF3 sF3
       grind)
    | exact superpose eq204 eq606
    | exact resolve eq606 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq612 : (M.op y (M.op y y)) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq608
       have i₂ := eq204 y y
       grind)
    | exact superpose eq204 eq608
    | exact resolve eq608 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq613 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq610 X0 X1
       have i₂ := eq609 X1 X0
       grind)
    | exact superpose eq609 eq610
    | exact resolve eq610 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq614 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq593 X2 (M.op X0 X1)
       have i₂ := eq204 X1 X0
       grind)
    | exact superpose eq204 eq593
    | exact resolve eq593 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq593 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq593 (M.op X0 X0) X0
       grind)
    | exact superpose eq593 eq593
    | exact resolve eq593 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq611 eq593
    | exact resolve eq593 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq210
       grind)
    | exact superpose eq210 eq40
    | exact resolve eq40 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq661
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq661
    | exact resolve eq661 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq664 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq662
    | exact resolve eq662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq672 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq613 (M.op X0 X0) X1
       have i₂ := eq593 (M.op X0 X0) X0
       grind)
    | exact superpose eq593 eq613
    | exact resolve eq613 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq204 X0 X0
       grind)
    | exact superpose eq204 eq672
    | exact resolve eq672 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq697 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X1 X2
       have i₂ := eq691 X1 X0
       grind)
    | (have i₁ := eq691 X0 X1
       have i₂ := eq691 X0 X0
       grind)
    | exact superpose eq691 eq691
    | exact resolve eq691 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq593 X1 X1
       have i₂ := eq691 X1 X0
       grind)
    | (have i₁ := eq593 X0 X0
       have i₂ := eq691 X0 X0
       grind)
    | exact superpose eq691 eq593
    | exact resolve eq593 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq612
       have i₂ := eq691 y X0
       grind)
    | (have i₁ := eq612
       have i₂ := eq691 y y
       grind)
    | exact superpose eq691 eq612
    | exact resolve eq612 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq715 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq611
       have i₂ := eq691 sF3 x
       grind)
    | (have i₁ := eq611
       have i₂ := eq691 sF3 sF3
       grind)
    | exact superpose eq691 eq611
    | exact resolve eq611 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq774 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq706 X0 X1
       grind)
    | exact superpose eq706 eq12
    | (have j0 := eq12 (M.op X1 (M.op X1 X0)) X0
       grind)
    | (have r₁ := eq12 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq706 X0 X1
       grind)
    | exact resolve eq12 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq615 X0
       grind)
    | exact superpose eq615 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq615 X0
       grind)
    | exact resolve eq12 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq633 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq633
       grind)
    | exact resolve eq12 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by grind
  clear eq790
  have eq793 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq778 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq795 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq774 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq796 : (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have j1 := eq13 (σ y) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq791
       have r₂ := eq13 (σ y) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq791
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ y)
       grind)
    | (have r₁ := eq791
       have r₂ := eq13 (σ y) (k (σ y) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq791 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq798 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq793 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq793 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | (have r₁ := eq793 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq793 X0
       have r₂ := eq13 (M.op X0 X0) (k (M.op X0 X0) X0)
       grind)
    | exact resolve eq793 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq799 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq795 X0 X1
       have j1 := eq13 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq795 X1 X1
       have r₂ := eq13 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq795 X0 X1
       have r₂ := eq13 X0 (M.op X1 (M.op X1 X0))
       grind)
    | (have r₁ := eq795 X1 X1
       have r₂ := eq13 (k X1 (M.op X1 (M.op X1 X1))) X1
       grind)
    | exact resolve eq795 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq828 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq40 (M.op x x)
       have i₂ := eq798 x
       grind)
    | exact superpose eq798 eq40
    | exact resolve eq40 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42 (M.op sF0 sF0)
       have i₂ := eq798 sF0
       grind)
    | exact superpose eq798 eq42
    | exact resolve eq42 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq38 (M.op x (M.op x sF0))
       have i₂ := eq799 sF0 x
       grind)
    | exact superpose eq799 eq38
    | exact resolve eq38 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq916 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq20 eq909
    | (have j0 := eq909 X0
       grind)
    | exact resolve eq909 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1429 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ (k X0 X1)) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq208 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq208
    | (have j0 := eq208 (σ X0) (σ X1)
       grind)
    | exact resolve eq208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (k X0 X1) (k X0 X1)) (M.op (k X0 X1) (k X0 X1)))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 (M.op (k X0 X1) (k X0 X1)) X1
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq204
    | (have j1 := eq208 X0 X1
       grind)
    | exact resolve eq204 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (k X0 X1) (M.op (k X0 X1) (k X0 X1)))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1452 X0 X1
       have i₂ := eq204 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq204 eq1452
    | (have j0 := eq1452 X0 X1
       grind)
    | exact resolve eq1452 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1466 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (k X0 X1) (M.op X1 (M.op X0 X0)))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq583 eq1463
    | (have j0 := eq1463 X0 X1
       have j1 := eq583 X0 X1
       grind)
    | exact resolve eq1463 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq664 eq211
    | exact resolve eq211 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1644
       have r₂ := eq27
       grind)
    | exact resolve eq1644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1660 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1653 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1653
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1653
       grind)
    | exact resolve eq12 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq1668 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq1660
  have eq1669 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq1668
  have eq1674 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1669
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq1669
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1669
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq1669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1679 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1674 eq664
    | exact resolve eq664 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1683 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1674 eq156
    | exact resolve eq156 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1686 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1679
  have eq1688 : y = (k y x) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq31 eq1683
    | exact resolve eq1683 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1691 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1688
       have r₂ := eq13 y (k y x)
       grind)
    | (have r₁ := eq1688
       have r₂ := eq13 (k y x) y
       grind)
    | (have r₁ := eq1688
       have r₂ := eq13 y (M.op y x)
       grind)
    | exact resolve eq1688 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1696 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq210
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq210
    | exact resolve eq210 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1698 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq40
    | exact resolve eq40 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1703 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1696
  have eq1706 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1698
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1698
    | exact resolve eq1698 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1713 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1706 eq211
    | exact resolve eq211 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1730 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1686
       grind)
    | exact superpose eq1686 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1686
       grind)
    | exact resolve eq12 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1731 : x = (M.op y (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq1686
       grind)
    | exact superpose eq1686 eq16
    | exact resolve eq16 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : x = (M.op x (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq706 y x
       have i₂ := eq1686
       grind)
    | exact superpose eq1686 eq706
    | exact resolve eq706 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1738 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1730
  have eq1739 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1738
  have eq1742 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1736
       have i₂ := eq221
       grind)
    | exact superpose eq221 eq1736
    | exact resolve eq1736 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1743 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1731
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq1731
    | exact resolve eq1731 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1744 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1739
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq1739
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1739
       have r₂ := eq13 y (k y x)
       grind)
    | exact resolve eq1739 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1750 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1744
       grind)
    | exact superpose eq1744 eq40
    | exact resolve eq40 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1753 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1750
    | exact resolve eq1750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1759 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1753 eq211
    | exact resolve eq211 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1753 eq208
    | (have j0 := eq208 (σ y) (σ x)
       grind)
    | exact resolve eq208 eq1753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1767 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq224 eq1764
    | exact resolve eq1764 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1771 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1759 eq1767
    | exact resolve eq1767 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1775 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1776 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1703
       grind)
    | exact resolve eq12 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1777 : x = (M.op y (M.op y y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq16
    | exact resolve eq16 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1782 : x = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq706 y x
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq706
    | exact resolve eq706 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1784 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1776
  have eq1785 : x = y ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1784
  have eq1786 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1775
  have eq1788 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1782
       have i₂ := eq221
       grind)
    | exact superpose eq221 eq1782
    | exact resolve eq1782 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq1782
  have eq1789 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1777
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq1777
    | exact resolve eq1777 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1790 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1785
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq1785
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1785
       have r₂ := eq13 y (k y x)
       grind)
    | exact resolve eq1785 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1791 : y = (k x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1786
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1786
    | exact resolve eq1786 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1796 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq40
    | exact resolve eq40 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1801 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1796
    | exact resolve eq1796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1807 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1801 eq211
    | exact resolve eq211 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1819 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1742 eq830
    | exact resolve eq830 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1821 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1742 eq202
    | exact resolve eq202 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1819
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1819
    | exact resolve eq1819 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1845 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1743 eq916
    | exact resolve eq916 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1852 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1743 eq697
    | exact resolve eq697 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1858 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1821 eq1852
    | exact resolve eq1852 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1862 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1821 eq1845
    | exact resolve eq1845 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1865 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1862
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1862
    | exact resolve eq1862 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1866 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq1865
       have r₂ := eq13 (σ (M.op x y)) (k (σ (M.op x y)) (σ y))
       grind)
    | (have r₁ := eq1865
       have r₂ := eq13 (k (σ (M.op x y)) (σ y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq1865
       have r₂ := eq13 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq1865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1869 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) y) ∨ x = y := by
    first
    | exact superpose eq1866 eq168
    | exact resolve eq168 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1871 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1866 eq208
    | (have j0 := eq208 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq208 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1872 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq28 eq1869
    | exact resolve eq1869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1886 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1788 eq202
    | exact resolve eq202 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1891 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op (M.op x y) x))) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1788 eq613
    | exact resolve eq613 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1788 eq204
    | exact resolve eq204 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1789 eq697
    | exact resolve eq697 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1918 : (M.op x y) = (M.op (M.op x y) (M.op x x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1789 eq706
    | exact resolve eq706 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq1922 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq1918
    | exact resolve eq1918 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1923 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1886 eq1917
    | exact resolve eq1917 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq1939 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq204 x x
       have i₂ := eq1821
       grind)
    | exact superpose eq1821 eq204
    | exact resolve eq204 eq1821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1948 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1939
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1939
    | exact resolve eq1939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq2003 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) X0) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X1 X1)) X0
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X1)) X0
       have j1 := eq217 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X1 X1)) X0
       have r₂ := eq217 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq217 X0 X1
       grind)
    | exact resolve eq12 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2004 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) = X0 ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq16
    | (have j1 := eq217 X0 X1
       grind)
    | exact resolve eq16 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X0)) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq204
    | (have j1 := eq217 X0 X1
       grind)
    | exact resolve eq204 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq2031 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) X0) ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2003 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2032 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) X0) ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2031 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2060 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X0)) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X0 X1
       have i₂ := eq204 (M.op X1 X1) X0
       grind)
    | exact superpose eq204 eq2005
    | (have j0 := eq2005 X0 X1
       grind)
    | exact resolve eq2005 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2061 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X0) = X1 ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X0 X1
       have i₂ := eq614 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq614 eq2004
    | (have j0 := eq2004 X0 X1
       grind)
    | exact resolve eq2004 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2062 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) X0) ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2032 X0 X1
       have j1 := eq13 (M.op X0 (M.op X1 X1)) X0
       grind)
    | (have r₁ := eq2032 X1 X1
       have r₂ := eq13 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq2032 X0 X1
       have r₂ := eq13 X0 (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq2032 X0 X1
       have r₂ := eq13 (M.op X0 (M.op X1 X1)) (k (M.op X0 (M.op X1 X1)) X0)
       grind)
    | exact resolve eq2032 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2090 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X0)) ∨ (M.op X0 (M.op X1 X1)) = X0 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2060 X0 X1
       have i₂ := eq204 X1 X1
       grind)
    | exact superpose eq204 eq2060
    | (have j0 := eq2060 X0 X1
       grind)
    | exact resolve eq2060 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2295 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq613 y x
       have i₂ := eq1948
       grind)
    | exact superpose eq1948 eq613
    | exact resolve eq613 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2299 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq204 y y
       have i₂ := eq1948
       grind)
    | exact superpose eq1948 eq204
    | exact resolve eq204 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq2306 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1742 eq2299
    | exact resolve eq2299 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq2740 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1886
       have i₂ := eq1895
       grind)
    | exact superpose eq1895 eq1886
    | exact resolve eq1886 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895
  have eq2761 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2740
  have eq3177 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1759 eq706
    | exact resolve eq706 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq3183 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq224 eq3177
    | exact resolve eq3177 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3225 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1807 eq16
    | exact resolve eq16 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq3237 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq715 eq3225
    | exact resolve eq3225 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3241 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3183 eq203
    | exact resolve eq203 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183
  have eq4898 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1713 eq16
    | exact resolve eq16 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq4915 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq715 eq4898
    | exact resolve eq4898 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq4921 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3237 eq4915
    | exact resolve eq4915 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237 eq4915
  have eq5154 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4921 eq796
    | exact resolve eq796 eq4921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq4921
  have eq5173 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq5154
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq5154
       have r₂ := eq13 (k (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq5154
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq5154 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5182 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5173 eq156
    | exact resolve eq156 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq5173
  have eq5187 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq31 eq5182
    | exact resolve eq5182 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5182
  have eq5229 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq5187 eq706
    | exact resolve eq706 eq5187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5187
  have eq5234 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq202 eq5229
    | exact resolve eq5229 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq5229
  have eq5242 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq5234
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq5234
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq5234
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq5234 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234
  have eq5246 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5242
       grind)
    | exact superpose eq5242 eq40
    | exact resolve eq40 eq5242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5242
  have eq5250 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5246
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5246
    | exact resolve eq5246 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5250 eq211
    | exact resolve eq211 eq5250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq5250
  have eq5263 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5257
  have eq5274 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq16
    | exact resolve eq16 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5275 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq204
    | exact resolve eq204 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5279 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq706
    | exact resolve eq706 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5285 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq224 eq5279
    | exact resolve eq5279 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5279
  have eq5286 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq715 eq5274
    | exact resolve eq5274 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5274
  have eq5289 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5285 eq203
    | exact resolve eq203 eq5285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq5321 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5286 eq697
    | exact resolve eq697 eq5286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286
  have eq5326 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5289 eq5321
    | exact resolve eq5321 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5321
  have eq5354 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5289 eq204
    | exact resolve eq204 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5363 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq5354
    | exact resolve eq5354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq5415 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5363 eq204
    | exact resolve eq204 eq5363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5424 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5285 eq5415
    | exact resolve eq5415 eq5285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415
  have eq5658 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5326 eq706
    | exact resolve eq706 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326
  have eq9839 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5658 eq706
    | exact resolve eq706 eq5658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5658
  have eq9868 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9839 x
       have i₂ := eq204 sF4 x
       grind)
    | exact superpose eq204 eq9839
    | exact resolve eq9839 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9839
  have eq9897 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5285 eq9868
    | exact resolve eq9868 eq5285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5285 eq9868
  have eq11572 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1871 eq16
    | exact resolve eq16 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11586 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1871 eq11572
    | exact resolve eq11572 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq11572
  have eq11620 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11586 eq9897
    | exact resolve eq9897 eq11586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897
  have eq11627 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11586 eq16
    | exact resolve eq16 eq11586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11629 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11586 eq604
    | exact resolve eq604 eq11586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11586
  have eq11642 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11629
       have i₂ := eq613 sF3 sF1
       grind)
    | exact superpose eq613 eq11629
    | exact resolve eq11629 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11629
  have eq11643 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11620
       have i₂ := eq691 sF2 sF1
       grind)
    | exact superpose eq691 eq11620
    | exact resolve eq11620 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11620
  have eq11644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3241 eq11643
    | exact resolve eq11643 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241 eq11643
  have eq11645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq11644
    | exact resolve eq11644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11644
  have eq11646 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11645
       have r₂ := eq27
       grind)
    | exact resolve eq11645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11645
  have eq11661 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11642 eq1771
    | exact resolve eq1771 eq11642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq11642
  have eq11697 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq11661
  have eq14081 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) = (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X1 (M.op X1 X1)
       have i₂ := eq691 X1 X0
       grind)
    | (have i₁ := eq609 X1 (M.op X1 X0)
       have i₂ := eq691 X0 X1
       grind)
    | exact superpose eq691 eq609
    | exact resolve eq609 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq14284 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5289 eq609
    | exact resolve eq609 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq5289
  have eq14514 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq14284
    | (have j0 := eq14284 X0
       grind)
    | exact resolve eq14284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14284
  have eq14703 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X1) = (M.op X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14081 X0 X1
       have i₂ := eq16 X1 X1
       grind)
    | exact superpose eq16 eq14081
    | exact resolve eq14081 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14081
  have eq14958 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14703 X0 X1
       have i₂ := eq593 (M.op X1 X1) X1
       grind)
    | exact superpose eq593 eq14703
    | exact resolve eq14703 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14703
  have eq17042 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11697 eq16
    | exact resolve eq16 eq11697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17044 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ x))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11697 eq604
    | exact resolve eq604 eq11697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17049 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11697 eq706
    | exact resolve eq706 eq11697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq11697
  have eq17068 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq224 eq17049
    | exact resolve eq17049 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq17049
  have eq17073 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq17044
       have i₂ := eq613 sF2 sF3
       grind)
    | exact superpose eq613 eq17044
    | exact resolve eq17044 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17044
  have eq17075 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq715 eq17042
    | exact resolve eq17042 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17042
  have eq17079 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11646 eq17068
    | exact resolve eq17068 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17068
  have eq17082 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq11646 eq17075
    | exact resolve eq17075 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11646 eq17075
  have eq17088 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq17082
    | exact resolve eq17082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082
  have eq17165 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17073 eq697
    | exact resolve eq697 eq17073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17073
  have eq17192 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq17165
    | (have j0 := eq17165 X0
       grind)
    | exact resolve eq17165 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17165
  have eq17206 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17088 eq17192
    | exact resolve eq17192 eq17088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17088 eq17192
  have eq17262 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq17079 eq593
    | exact resolve eq593 eq17079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17079
  have eq17322 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq17206 eq17262
    | exact resolve eq17262 eq17206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17206 eq17262
  have eq17323 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17322
  have eq21106 : ∀ X0 : G, (σ y) = (k (M.op X0 (M.op (σ x) (σ y))) X0) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5363 eq2061
    | (have j0 := eq2061 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2061 eq5363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5363
  have eq21124 : (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1891 eq2061
    | (have j0 := eq2061 (M.op (M.op x y) x) (M.op (M.op x y) x)
       grind)
    | exact resolve eq2061 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq21130 : (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2295 eq2061
    | (have j0 := eq2061 (M.op y (M.op x y)) (M.op y (M.op x y))
       grind)
    | exact resolve eq2061 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq21192 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11627 eq2061
    | (have j0 := eq2061 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2061 eq11627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq11627
  have eq21222 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq21192
  have eq21250 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq17323 eq21222
    | exact resolve eq21222 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323 eq21222
  have eq21295 : (M.op y (M.op (M.op x y) (M.op x y))) = (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21130
       have i₂ := eq204 sF0 y
       grind)
    | exact superpose eq204 eq21130
    | exact resolve eq21130 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21130
  have eq21301 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x x)) ∨ (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21124
       have i₂ := eq204 x sF0
       grind)
    | exact superpose eq204 eq21124
    | exact resolve eq21124 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21124
  have eq21310 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1836 eq21250
    | exact resolve eq21250 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq21250
  have eq21346 : (M.op y x) = (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1742 eq21295
    | exact resolve eq21295 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742 eq21295
  have eq21352 : (M.op (M.op x y) x) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq21301
    | exact resolve eq21301 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq21301
  have eq21383 : y = (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1686 eq21346
    | exact resolve eq21346 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686 eq21346
  have eq21386 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1922 eq21352
    | exact resolve eq21352 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq21352
  have eq21405 : x = y ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2306 eq21383
    | exact resolve eq21383 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21383
  have eq21406 : x = y ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21405
  have eq21410 : y = (M.op x y) ∨ (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2761 eq21386
    | exact resolve eq21386 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21386
  have eq21411 : y = (M.op x y) ∨ (M.op (M.op x y) x) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq21410
  have eq21421 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (k (M.op x y) x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2306 eq21406
    | exact resolve eq21406 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21406
  have eq21424 : y = (M.op x y) ∨ y = (k x y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq2761 eq21411
    | exact resolve eq21411 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761 eq21411
  have eq21432 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1791 eq21424
    | exact resolve eq21424 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791 eq21424
  have eq21616 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X1 ∨ (k (M.op X0 (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq22277 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21432 eq1923
    | exact resolve eq1923 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923 eq21432
  have eq22327 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ y = (k x y) := by grind
  clear eq22277
  have eq22356 : x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq1788 eq22327
    | exact resolve eq22327 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq22327
  have eq22357 : y = (k x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq22356
  have eq22420 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (k (M.op x y) x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21421 eq1858
    | exact resolve eq1858 eq21421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq21421
  have eq22468 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (k (M.op x y) x) := by grind
  clear eq22420
  have eq22504 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2306 eq22468
    | exact resolve eq22468 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306 eq22468
  have eq22505 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq22504
  have eq22535 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22505 eq38
    | exact resolve eq38 eq22505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq22505
  have eq22549 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22535
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22535
    | exact resolve eq22535 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22535
  have eq22990 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22549 eq1466
    | (have j0 := eq1466 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1466 eq22549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq23313 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22990
       have i₂ := eq614 sF2 sF1 sF2
       grind)
    | exact superpose eq614 eq22990
    | exact resolve eq22990 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq22990
  have eq23448 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11 eq23313
    | (have j1 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq23313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23313
  have eq23559 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21310 eq23448
    | exact resolve eq23448 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310 eq23448
  have eq23633 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq23559
       have r₂ := eq13 (σ (M.op x y)) (k (σ (M.op x y)) (σ x))
       grind)
    | (have r₁ := eq23559
       have r₂ := eq13 (k (σ (M.op x y)) (σ x)) (σ (M.op x y))
       grind)
    | (have r₁ := eq23559
       have r₂ := eq13 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))
       grind)
    | exact resolve eq23559 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23559
  have eq23663 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22549 eq23633
    | exact resolve eq23633 eq22549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23633
  have eq24625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23663 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq23663
       grind)
    | exact resolve eq12 eq23663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23663
  have eq24635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq24625
  have eq24636 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq24635
  have eq24656 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq24636
       have r₂ := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq24636
       have r₂ := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq24636
       have r₂ := eq13 (σ (M.op x y)) (k (σ (M.op x y)) (σ x))
       grind)
    | exact resolve eq24636 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24636
  have eq24678 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq22549 eq24656
    | exact resolve eq24656 eq22549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22549 eq24656
  have eq24681 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq24678 eq28
    | exact resolve eq28 eq24678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24678
  have eq24737 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq24681
    | exact resolve eq24681 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24681
  have eq24758 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24737 eq147
    | exact resolve eq147 eq24737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq24737
  have eq24844 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq113 eq24758
    | exact resolve eq24758 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq24758
  have eq24861 : y = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22357 eq24844
    | exact resolve eq24844 eq22357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22357 eq24844
  have eq24866 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1872 eq24861
    | exact resolve eq24861 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872 eq24861
  have eq24867 : y = (M.op x y) ∨ x = y := by grind
  clear eq24866
  have eq24870 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq24867
       grind)
    | exact superpose eq24867 eq18
    | exact resolve eq18 eq24867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24871 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq24867
       grind)
    | exact superpose eq24867 eq24
    | exact resolve eq24 eq24867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24919 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq24867
  have eq24943 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq24871
    | exact resolve eq24871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24871
  have eq29797 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ y) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14514 eq2090
    | exact resolve eq2090 eq14514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14514
  have eq29900 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq604 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)
       have i₂ := eq2090 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq2090 eq604
    | (have j1 := eq2090 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact resolve eq604 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq29980 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29900 x
       have i₂ := eq593 (M.op x x) x
       grind)
    | exact superpose eq593 eq29900
    | (have j0 := eq29900 X0
       grind)
    | exact resolve eq29900 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29900
  have eq30022 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ y) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29797
       have i₂ := eq204 sF2 sF3
       grind)
    | exact superpose eq204 eq29797
    | exact resolve eq29797 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29797
  have eq30099 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29980 X0
       have i₂ := eq593 X0 X0
       grind)
    | exact superpose eq593 eq29980
    | (have j0 := eq29980 X0
       grind)
    | exact resolve eq29980 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29980
  have eq30138 : (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq715 eq30022
    | exact resolve eq30022 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq30022
  have eq30203 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30099 X0
       have i₂ := eq14958 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14958 eq30099
    | (have j0 := eq30099 X0
       grind)
    | exact resolve eq30099 eq14958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14958 eq30099
  have eq30234 : (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq30138
    | exact resolve eq30138 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30138
  have eq30272 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30203 X0
       have i₂ := eq593 (M.op X0 X0) X0
       grind)
    | exact superpose eq593 eq30203
    | (have j0 := eq30203 X0
       grind)
    | exact resolve eq30203 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30203
  have eq30291 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq633 eq30234
    | exact resolve eq30234 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq30234
  have eq30332 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30272 X0
       have i₂ := eq204 X0 X0
       grind)
    | exact superpose eq204 eq30272
    | (have j0 := eq30272 X0
       grind)
    | exact resolve eq30272 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq30272
  have eq30333 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq30332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30332
  have eq30344 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq30291
    | exact resolve eq30291 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30291
  have eq30372 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq30333 x
       have i₂ := eq593 (M.op x x) x
       grind)
    | exact superpose eq593 eq30333
    | (have j0 := eq30333 X0
       grind)
    | exact resolve eq30333 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30333
  have eq30381 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5263 eq30344
    | exact resolve eq30344 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263 eq30344
  have eq30406 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30372 X0
       have j1 := eq21616 X0 X0
       grind)
    | (have r₁ := eq30372 x
       have r₂ := eq21616 x x
       grind)
    | exact resolve eq30372 eq21616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21616 eq30372
  have eq30411 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5275 eq30381
    | exact resolve eq30381 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275 eq30381
  have eq30434 : (σ y) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21106 eq30411
    | (have j1 := eq21106 (σ y)
       grind)
    | exact resolve eq30411 eq21106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21106 eq30411
  have eq30454 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5424 eq30434
    | exact resolve eq30434 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30434
  have eq30464 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq30454
    | exact resolve eq30454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30454
  have eq30465 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq30464
  have eq30475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5424 eq30465
    | exact resolve eq30465 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30465
  have eq30476 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by grind
  clear eq30475
  have eq30478 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5424 eq30476
    | exact resolve eq30476 eq5424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424 eq30476
  have eq31292 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30478 eq105
    | exact resolve eq105 eq30478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30478
  have eq31315 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq31292
    | exact resolve eq31292 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31292
  have eq31335 : x = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq208 x y
       have i₂ := eq31315
       grind)
    | exact superpose eq31315 eq208
    | (have j0 := eq208 x y
       grind)
    | exact resolve eq208 eq31315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31315
  have eq31338 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31335
       have i₂ := eq713 y
       grind)
    | exact superpose eq713 eq31335
    | exact resolve eq31335 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq31335
  have eq31349 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31338
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31338
    | exact resolve eq31338 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31338
  have eq31359 : x = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31349
       have r₂ := eq24919
       grind)
    | exact resolve eq31349 eq24919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31349
  have eq31367 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24870 eq31359
    | exact resolve eq31359 eq24870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24870 eq31359
  have eq31370 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31367
       have r₂ := eq24919
       grind)
    | exact resolve eq31367 eq24919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24919 eq31367
  have eq31371 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31370 eq27
    | exact resolve eq27 eq31370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31370
  have eq31510 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31371
       have r₂ := eq24943
       grind)
    | exact resolve eq31371 eq24943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24943 eq31371
  have eq31539 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31510 eq31
    | exact resolve eq31 eq31510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31510
  have eq31646 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq31539
    | exact resolve eq31539 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31539
  have eq31647 : x = y := by grind
  clear eq31646
  have eq31665 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31647
       grind)
    | exact superpose eq31647 eq18
    | exact resolve eq18 eq31647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31666 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31647
       grind)
    | exact superpose eq31647 eq24
    | exact resolve eq24 eq31647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31647
  have eq31703 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31666
    | exact resolve eq31666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31666
  have eq31704 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31703 eq26
    | exact resolve eq26 eq31703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31703
  have eq31793 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq828
       have i₂ := eq31665
       grind)
    | exact superpose eq31665 eq828
    | exact resolve eq828 eq31665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq31822 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq593 X0 x
       have i₂ := eq31665
       grind)
    | exact superpose eq31665 eq593
    | exact resolve eq593 eq31665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31826 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq615 x
       have i₂ := eq31665
       grind)
    | exact superpose eq31665 eq615
    | exact resolve eq615 eq31665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq31828 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq798 x
       have i₂ := eq31665
       grind)
    | exact superpose eq31665 eq798
    | exact resolve eq798 eq31665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq31665
  have eq31854 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq31793
    | exact resolve eq31793 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31793
  have eq31922 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq31704 eq593
    | exact resolve eq593 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32038 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq31828 eq1429
    | (have j0 := eq1429 (M.op x y) x
       grind)
    | exact resolve eq1429 eq31828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429 eq31828
  have eq32049 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq32038
    | exact resolve eq32038 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32038
  have eq32052 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32049
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32049
    | exact resolve eq32049 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32049
  have eq32054 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq32052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32052
    | exact resolve eq32052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32052
  have eq32055 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq32054
    | exact resolve eq32054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32054
  have eq32056 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq32055
    | exact resolve eq32055 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32055
  have eq32057 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32056
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32056
    | exact resolve eq32056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32056
  have eq32075 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31854 eq583
    | (have j0 := eq583 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq583 eq31854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31854
  have eq32078 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32057 eq32075
    | exact resolve eq32075 eq32057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32057 eq32075
  have eq32723 : ∀ X0 : G, x = (M.op X0 (k (M.op x y) X0)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq31822 x
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq31822
    | (have j1 := eq11 (M.op x y) X0
       grind)
    | exact resolve eq31822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ x))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32078 eq604
    | exact resolve eq604 eq32078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq32078
  have eq37607 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37587
       have i₂ := eq613 sF2 sF1
       grind)
    | exact superpose eq613 eq37587
    | exact resolve eq37587 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq37587
  have eq37613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31704 eq37607
    | exact resolve eq37607 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37607
  have eq37616 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq37613
       have r₂ := eq27
       grind)
    | exact resolve eq37613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37613
  have eq37636 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq37616 eq593
    | exact resolve eq593 eq37616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq40581 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31922 eq30406
    | exact resolve eq30406 eq31922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31922
  have eq40609 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq30406 sF0
       grind)
    | exact superpose eq30406 eq42
    | exact resolve eq42 eq30406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq30406
  have eq40618 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq31822 eq40609
    | exact resolve eq40609 eq31822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40609
  have eq40645 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq40618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40618
    | exact resolve eq40618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40618
  have eq40654 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq40645
    | exact resolve eq40645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40645
  have eq41311 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40654 eq208
    | (have j0 := eq208 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq208 eq40654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq40654
  have eq41314 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37616 eq41311
    | exact resolve eq41311 eq37616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41311
  have eq41369 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq40581 eq105
    | exact resolve eq105 eq40581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq40581
  have eq41818 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq41314 eq697
    | exact resolve eq697 eq41314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq41314
  have eq41834 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq31704 eq41818
    | exact resolve eq41818 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31704 eq41818
  have eq41851 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq37616 eq41834
    | (have j0 := eq41834 X0
       grind)
    | exact resolve eq41834 eq37616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37616 eq41834
  have eq41852 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq41851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41851
  have eq41857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f41857_13 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      grind
    have f41857_14 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      grind
    have f41857_23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x y)) := by grind
    have f41857_24 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f41857_26 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
      intro X0
      first
      | (have j0 := f41857_14 X0
         grind)
      | (have r₁ := f41857_14 X0
         have r₂ := f41857_24
         grind)
      | exact resolve f41857_14 f41857_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f41857_27 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) := by
      intro X0
      first
      | (have j0 := f41857_13 X0
         grind)
      | (have r₁ := f41857_13 X0
         have r₂ := f41857_24
         grind)
      | exact resolve f41857_13 f41857_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f41857_28 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
      first
      | (have i₁ := f41857_27 x
         have i₂ := f41857_26 x
         grind)
      | exact superpose f41857_26 f41857_27
      | exact resolve f41857_27 f41857_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f41857_29 : False := by
      first
      | (have r₁ := f41857_28
         have r₂ := f41857_23
         grind)
      | exact resolve f41857_28 f41857_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f41857_29
  clear eq37636 eq41852
  have eq41859 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq41857
       have r₂ := eq27
       grind)
    | exact resolve eq41857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41857
  have eq41863 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq41859 eq28
    | exact resolve eq28 eq41859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq41859
  have eq41953 : x = (M.op x y) := by
    first
    | exact superpose eq41863 eq29
    | exact resolve eq29 eq41863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41863
  have eq42108 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31826
       have i₂ := eq41953
       grind)
    | exact superpose eq41953 eq31826
    | exact resolve eq31826 eq41953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31826
  have eq42131 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq41369
       have i₂ := eq41953
       grind)
    | exact superpose eq41953 eq41369
    | exact resolve eq41369 eq41953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41369
  have eq43424 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq42131 eq32723
    | (have j0 := eq32723 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq32723 eq42131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32723
  have eq43432 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq42131 eq583
    | (have j0 := eq583 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq583 eq42131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq43437 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq42108 eq43432
    | exact resolve eq43432 eq42108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42108 eq43432
  have eq43445 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq43424
       have i₂ := eq41953
       grind)
    | exact superpose eq41953 eq43424
    | exact resolve eq43424 eq41953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43424
  have eq43446 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11 eq43437
    | (have j1 := eq11 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq43437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43437
  have eq43454 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq42131 eq43446
    | exact resolve eq43446 eq42131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42131 eq43446
  have eq43459 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43445 eq43454
    | exact resolve eq43454 eq43445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43445 eq43454
  have eq43460 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq43459
  have eq46261 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43460 eq16
    | exact resolve eq16 eq43460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43460
  have eq46281 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31822 eq46261
    | exact resolve eq46261 eq31822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31822 eq46261
  have eq46290 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq46281
       have i₂ := eq41953
       grind)
    | exact superpose eq41953 eq46281
    | exact resolve eq46281 eq41953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41953 eq46281
  have eq46291 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq46290
  have eq46319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46291 eq14
    | exact resolve eq14 eq46291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46291
  have eq46336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq46319
    | exact resolve eq46319 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46319
  have eq46342 : False := by grind
  exact eq46342
