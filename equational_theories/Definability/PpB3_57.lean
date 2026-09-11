import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ X3 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X1 X0)) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq9 X0 X1 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq115 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq115 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq115 X1 X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | exact resolve eq115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq132 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1 x x
       have j1 := eq43 X0 X1 X1 X0
       grind)
    | (have r₁ := eq94 x x X0 X1
       have r₂ := eq43 X0 X1 x x
       grind)
    | (have r₁ := eq94 (M.op (M.op X0 X1) (M.op X0 x)) X1 x x
       have r₂ := eq43 X0 X1 x (M.op (M.op x x) (M.op x X1))
       grind)
    | (have r₁ := eq94 (M.op X0 x) X1 x x
       have r₂ := eq43 X0 x x (M.op X1 (M.op X0 x))
       grind)
    | exact resolve eq94 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq94
  have eq576 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq580 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq576 X0 X1
       have j1 := eq132 X0 X1
       grind)
    | (have r₁ := eq576 X0 X1
       have r₂ := eq132 X0 X1
       grind)
    | (have r₁ := eq576 X0 X0
       have r₂ := eq132 X0 X0
       grind)
    | exact resolve eq576 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq576
  have eq624 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq580 (σ X1) (σ X0)
       grind)
    | exact superpose eq580 eq15
    | exact resolve eq15 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq624
    | exact resolve eq624 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq624
  have eq1202 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq631 x y
       grind)
    | exact superpose eq631 eq16
    | (have r₁ := eq16
       have r₂ := eq631 x y
       grind)
    | exact resolve eq16 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1233 : False := by grind
  exact eq1233

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq80 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  clear eq80
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have r₁ := eq12 (M.op X1 (M.op X1 X2)) (M.op X1 X2)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq213 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq370 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq547 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq281
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1951 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq73
    | exact resolve eq73 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq73
  have eq1995 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1951 X0
       have i₂ := eq14 (M.op x X0) sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq1951
    | exact resolve eq1951 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2017 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op x y) (M.op x X0)) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq1995 X0
       have i₂ := eq14 X0 x X0
       grind)
    | exact superpose eq14 eq1995
    | exact resolve eq1995 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq2796 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X1 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq120 X1 X2 X0
       grind)
    | exact superpose eq120 eq14
    | (have j1 := eq120 X1 X2 X0
       grind)
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq3382 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq17657 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2796 X0 x x
       have i₂ := eq213 x x X0
       grind)
    | (have i₁ := eq2796 x x y
       have i₂ := eq213 X0 x x
       grind)
    | exact superpose eq213 eq2796
    | (have j0 := eq2796 X0 x y
       grind)
    | exact resolve eq2796 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq2796
  have eq17914 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq17657 eq2017
    | (have j1 := eq17657 X0
       grind)
    | exact resolve eq2017 eq17657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017 eq17657
  have eq17968 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17914
  have eq18040 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq17968 (σ X0)
       grind)
    | exact superpose eq17968 eq10
    | exact resolve eq10 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18044 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq547 X0 X0
       have i₂ := eq17968 (τ X0)
       grind)
    | exact superpose eq17968 eq547
    | exact resolve eq547 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq18052 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17968 x
       grind)
    | exact superpose eq17968 eq44
    | exact resolve eq44 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq18091 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq17968 sF2
       grind)
    | exact superpose eq17968 eq50
    | exact resolve eq50 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq18123 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq18091
       have i₂ := eq17968 x
       grind)
    | exact superpose eq17968 eq18091
    | exact resolve eq18091 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq18161 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18052
       have i₂ := eq17968 sF2
       grind)
    | exact superpose eq17968 eq18052
    | exact resolve eq18052 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18052
  have eq18169 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18044 X0
       have i₂ := eq17968 X0
       grind)
    | exact superpose eq17968 eq18044
    | exact resolve eq18044 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq18173 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18040 X0
       have i₂ := eq17968 X0
       grind)
    | exact superpose eq17968 eq18040
    | exact resolve eq18040 eq17968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17968 eq18040
  have eq27917 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq18169 X0
       grind)
    | exact superpose eq18169 eq370
    | exact resolve eq370 eq18169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq18169
  have eq27918 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq27917 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq27917
    | exact resolve eq27917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27917
  have eq27919 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq27918
  have eq27930 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27919 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq27919
    | exact resolve eq27919 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27919
  have eq28239 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (τ (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq27930 X0
       have i₂ := eq18173 X0
       grind)
    | exact superpose eq18173 eq27930
    | exact resolve eq27930 eq18173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27930
  have eq28366 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28239 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq28239
    | exact resolve eq28239 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28239
  have eq87363 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3382 X0 X1
       have i₂ := eq18173 X0
       grind)
    | exact superpose eq18173 eq3382
    | (have j0 := eq3382 X0 X1
       grind)
    | exact resolve eq3382 eq18173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq87364 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87363 X0 X1
       have i₂ := eq18173 X0
       grind)
    | exact superpose eq18173 eq87363
    | (have j0 := eq87363 X0 X1
       grind)
    | exact resolve eq87363 eq18173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173 eq87363
  have eq101985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq101985
    | exact resolve eq101985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101985
  have eq101997 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq101986
       have r₂ := eq28
       grind)
    | exact resolve eq101986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101986
  have eq102001 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq101997
    | exact resolve eq101997 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101997
  have eq102005 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102001 eq116
    | (have r₁ := eq116
       have r₂ := eq102001
       grind)
    | exact resolve eq116 eq102001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq102195 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq102001
  have eq102197 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq102005
  have eq108041 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq102197
       have r₂ := eq102195
       grind)
    | exact resolve eq102197 eq102195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102195 eq102197
  have eq108094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq108041 eq101
    | exact resolve eq101 eq108041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq108041
  have eq108104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq108094
  have eq108107 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq108104
       have r₂ := eq28
       grind)
    | exact resolve eq108104 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108104
  have eq108116 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq108107 eq18123
    | exact resolve eq18123 eq108107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108107
  have eq108378 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq108116
    | exact resolve eq108116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108116
  have eq108379 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq108378
  have eq108421 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq108379
       grind)
    | exact superpose eq108379 eq115
    | (have r₁ := eq115
       have r₂ := eq108379
       grind)
    | exact resolve eq115 eq108379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq108430 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18161
       have i₂ := eq108379
       grind)
    | exact superpose eq108379 eq18161
    | exact resolve eq18161 eq108379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108656 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq108379
  have eq108658 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq108421
  have eq108761 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq108430
    | exact resolve eq108430 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108430
  have eq115440 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq108658
       have r₂ := eq108656
       grind)
    | exact resolve eq108658 eq108656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108656 eq108658
  have eq117000 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87364 x y
       have i₂ := eq115440
       grind)
    | exact superpose eq115440 eq87364
    | (have j0 := eq87364 x y
       grind)
    | exact resolve eq87364 eq115440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87364 eq115440
  have eq117004 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117000
       have i₂ := eq18161
       grind)
    | exact superpose eq18161 eq117000
    | exact resolve eq117000 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117000
  have eq117014 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq117004
    | exact resolve eq117004 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117004
  have eq117017 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq117014
       have r₂ := eq108761
       grind)
    | exact resolve eq117014 eq108761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108761 eq117014
  have eq117018 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117017
       have i₂ := eq18161
       grind)
    | exact superpose eq18161 eq117017
    | exact resolve eq117017 eq18161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18161 eq117017
  have eq117019 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117018
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq117018
    | exact resolve eq117018 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117018
  have eq117020 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq117019
    | exact resolve eq117019 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117019
  have eq117021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117020
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq117020
    | exact resolve eq117020 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117020
  have eq117022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117021
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq117021
    | exact resolve eq117021 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117021
  have eq117023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq117022
    | exact resolve eq117022 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117022
  have eq117024 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq117023
       have r₂ := eq28
       grind)
    | exact resolve eq117023 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117023
  have eq117069 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117024 eq18123
    | exact resolve eq18123 eq117024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123 eq117024
  have eq117352 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq117069
    | exact resolve eq117069 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq117069
  have eq117353 : y = (M.op x x) := by grind
  clear eq117352
  have eq117558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28366 x
       have i₂ := eq117353
       grind)
    | exact superpose eq117353 eq28366
    | exact resolve eq28366 eq117353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28366 eq117353
  have eq117668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117558
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq117558
    | exact resolve eq117558 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq117558
  have eq117724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117668
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq117668
    | exact resolve eq117668 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq117668
  have eq117736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq117724
    | exact resolve eq117724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq117724
  have eq117740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117736
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117736
    | exact resolve eq117736 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq117736
  have eq117742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq117740
    | exact resolve eq117740 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq117740
  have eq117744 : False := by grind
  exact eq117744

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_x_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 X3
       have i₂ := eq9 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ X2 ∨ (M.op X2 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq9 X0 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = X0 ∨ (M.op X3 X3) = X0 ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X3 : G, (M.op X3 X3) = X0 ∨ (M.op X0 X3) = (k X3 X0) := by
    intro X0 X3
    first
    | (have j0 := eq39 X0 x x X3
       have j1 := eq28 X0 x X0 X3
       grind)
    | (have r₁ := eq39 x X0 x X3
       have r₂ := eq28 X0 x x X3
       grind)
    | (have r₁ := eq39 x x x (M.op X0 x)
       have r₂ := eq28 X0 x x X3
       grind)
    | (have r₁ := eq39 (M.op (M.op X0 x) (M.op X0 (M.op X3 X3))) x x X3
       have r₂ := eq28 X0 x (M.op X3 X3) X3
       grind)
    | exact resolve eq39 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq171 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X2 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X0 X1 X3 X3
       have i₂ := eq56 X0 X3
       grind)
    | (have i₁ := eq26 X0 X1 X2 X3
       have i₂ := eq56 (M.op X2 X3) X3
       grind)
    | exact superpose eq56 eq26
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq26 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq56
  have eq230 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq171 X0 X1 x x
       have j1 := eq28 X0 X1 X0 X1
       grind)
    | (have r₁ := eq171 x X1 X0 X1
       have r₂ := eq28 X0 X1 x x
       grind)
    | exact resolve eq171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq171
  have eq761 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq230 (σ X0) (σ X1)
       grind)
    | exact superpose eq230 eq15
    | exact resolve eq15 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 X1
       have i₂ := eq230 X0 X1
       grind)
    | exact superpose eq230 eq761
    | exact resolve eq761 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq761
  have eq769 : False := by grind
  exact eq769

/-- `Equation3794`: `x ◇ y = (z ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyx_x_pyx_Equation3794 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3794 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3794.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X1) X3 (M.op X2 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X3 X0) X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) (M.op X3 X0)
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (k (M.op X2 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X0) (M.op X2 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X0) (M.op X2 X1)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq9 X1 X1 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X1 X0) = (k (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 X0 X1 X2
       grind)
    | (have r₁ := eq64 (M.op X2 X1) X1 (M.op X2 (M.op X2 X1))
       have r₂ := eq9 (M.op X2 X1) X1 X2
       grind)
    | (have r₁ := eq64 (M.op X2 X0) (M.op X2 (M.op X2 X0)) X0
       have r₂ := eq9 X0 (M.op X2 X0) X2
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq66 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68
    | (have j0 := eq68 X0
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq254 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq254
    | (have j0 := eq254 (σ X0) (σ X1)
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq254
    | (have j0 := eq254 (τ X0) (τ X1)
       grind)
    | exact resolve eq254 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq263 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq254 X1 (τ X0)
       grind)
    | exact superpose eq254 eq19
    | (have j1 := eq254 X1 (τ X0)
       grind)
    | exact resolve eq19 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq254 (τ X1) X0
       grind)
    | exact superpose eq254 eq18
    | (have j1 := eq254 (τ X1) X0
       grind)
    | exact resolve eq18 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) (σ X0)) = (σ (M.op X0 (k (τ X1) X2))) ∨ (M.op (k (τ X1) X2) (k (τ X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 X2 X0
       have i₂ := eq254 (k (τ X1) X2) X0
       grind)
    | exact superpose eq254 eq22
    | (have j1 := eq254 (k (τ X1) X2) X0
       grind)
    | exact resolve eq22 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq455 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq465 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X1 X0
       have i₂ := eq254 X1 X0
       grind)
    | exact superpose eq254 eq255
    | (have j0 := eq255 X1 X0
       have j1 := eq254 (σ X1) (σ X0)
       grind)
    | exact resolve eq255 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq255 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq455 X0
       grind)
    | exact superpose eq455 eq255
    | (have j0 := eq255 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq255 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq255 X1 X0
       grind)
    | exact superpose eq255 eq10
    | (have j1 := eq255 X1 X0
       grind)
    | exact resolve eq10 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq553 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ (M.op X0 X0)) X1 (σ (M.op X0 X0)) X2
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq62
    | exact resolve eq62 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ (M.op X0 X0)) X2)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (σ (M.op X0 X0)) X2 X1 (σ (M.op X0 X0))
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq63
    | exact resolve eq63 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555 X0 X1 X2
       have i₂ := eq9 X1 X2 (σ (M.op X0 X0))
       grind)
    | exact superpose eq9 eq555
    | exact resolve eq555 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq560 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 X1 X2
       have i₂ := eq9 X1 X2 (σ (M.op X0 X0))
       grind)
    | exact superpose eq9 eq553
    | exact resolve eq553 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq572 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X1 (σ (M.op X3 X3))) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq559 X3 (M.op (M.op X1 (σ (M.op X3 X3))) X0) X2
       have i₂ := eq63 (σ (M.op X3 X3)) X2 X0 X1
       grind)
    | exact superpose eq63 eq559
    | exact resolve eq559 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq615 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X1 (M.op (M.op X0 (σ (M.op X3 X3))) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq560 X3 X1 (M.op (M.op X0 (σ (M.op X3 X3))) X2)
       have i₂ := eq62 (σ (M.op X3 X3)) X1 X0 X2
       grind)
    | exact superpose eq62 eq560
    | exact resolve eq560 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X0 (σ (M.op X1 X1))) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 (σ (M.op X1 X1)))
       have i₂ := eq615 X0 (M.op (M.op X0 (σ (M.op X1 X1))) X2) X3 X1
       grind)
    | exact superpose eq615 eq9
    | exact resolve eq9 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 (σ (M.op X2 X2))) X3)) X4) = (M.op X3 (M.op X1 (M.op (M.op X0 (σ (M.op X5 X5))) X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq572 X3 X1 (M.op (M.op X0 (σ (M.op X5 X5))) X4) X2
       have i₂ := eq615 X0 (M.op (M.op X1 (σ (M.op X2 X2))) X3) X4 X5
       grind)
    | exact superpose eq615 eq572
    | exact resolve eq572 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq1349 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (σ (M.op X2 X2))) X3)) X4) = (M.op X3 (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1320 X0 X1 X2 X3 X4 x
       have i₂ := eq615 X0 X1 X4 x
       grind)
    | exact superpose eq615 eq1320
    | exact resolve eq1320 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1353 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1315 X0 x X2 X3
       have i₂ := eq615 X0 X0 X2 x
       grind)
    | exact superpose eq615 eq1315
    | exact resolve eq1315 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1412 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) X4)) = (M.op (M.op (M.op X1 X0) X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1349 X0 X1 x X3 X4
       have i₂ := eq615 X1 X0 X3 x
       grind)
    | exact superpose eq615 eq1349
    | exact resolve eq1349 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq1349
  have eq1445 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1353 X2 X0 (M.op (M.op X2 X2) X1)
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq1353
    | exact resolve eq1353 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X1 (M.op (M.op X0 (M.op X3 X3)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1353 X3 X1 (M.op (M.op X0 (M.op X3 X3)) X2)
       have i₂ := eq62 (M.op X3 X3) X1 X0 X2
       grind)
    | exact superpose eq62 eq1353
    | exact resolve eq1353 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1612 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X2 X2) X1)) X0) ∨ (τ X0) = (M.op (M.op (M.op X2 X2) X1) (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq263 X0 (M.op (M.op X2 X2) X1)
       have i₂ := eq1445 (τ X0) X1 X2
       grind)
    | exact superpose eq1445 eq263
    | (have j0 := eq263 X0 (M.op (M.op X2 X2) X1)
       grind)
    | exact resolve eq263 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 X1) ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (M.op X2 X2) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1612 X0 X1 X2
       have i₂ := eq9 X1 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq1612
    | (have j0 := eq1612 X0 X1 X2
       grind)
    | exact resolve eq1612 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1682 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (k (σ (M.op (M.op X2 X2) X1)) X0) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq263 eq1613
    | (have j0 := eq1613 X0 X1 X2
       have j1 := eq263 X0 X1
       grind)
    | exact resolve eq1613 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq1613
  have eq3759 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq256 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq3786 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3759 (M.op X0 X0)
       have i₂ := eq455 X0
       grind)
    | exact superpose eq455 eq3759
    | (have j0 := eq3759 (M.op X0 X0)
       grind)
    | exact resolve eq3759 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq3791 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3759 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq3759
    | (have j0 := eq3759 (σ X0)
       grind)
    | exact resolve eq3759 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759
  have eq3793 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3786 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq3794 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3791 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3791
    | (have j0 := eq3791 X0
       grind)
    | exact resolve eq3791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3797 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3794 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3794
    | (have j0 := eq3794 X0
       grind)
    | exact resolve eq3794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794
  have eq3854 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X2 (M.op (M.op X1 (τ (M.op X0 X0))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1446 X1 X2 X3 (τ (M.op X0 X0))
       have i₂ := eq3793 X0
       grind)
    | exact superpose eq3793 eq1446
    | exact resolve eq1446 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq13790 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) (M.op (τ X0) (τ X0))) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (τ X0) (M.op (τ X0) (τ X0))
       have j1 := eq69 X0
       grind)
    | (have r₁ := eq12 (τ X0) (M.op (τ X0) (τ X0))
       have r₂ := eq69 X0
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13792 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op (τ X0) X2)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op (τ X0) (τ X0)) X1 (τ X0) X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq62
    | (have j1 := eq69 X0
       grind)
    | exact resolve eq62 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq13805 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq13790 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13790
  have eq13809 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op X1 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) X2))) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13792 X0 X1 X2
       have i₂ := eq1412 (τ X0) (τ X0) X1 (M.op (τ X0) X2)
       grind)
    | exact superpose eq1412 eq13792
    | (have j0 := eq13792 X0 X1 X2
       grind)
    | exact resolve eq13792 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412 eq13792
  have eq13827 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op X1 (M.op (τ X0) X2)) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13809 X0 X1 X2
       have i₂ := eq1445 X1 (M.op (τ X0) X2) (τ X0)
       grind)
    | exact superpose eq1445 eq13809
    | (have j0 := eq13809 X0 X1 X2
       grind)
    | exact resolve eq13809 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq13809
  have eq17922 : ∀ X0 X1 X2 : G, (τ (k (σ X0) (σ X1))) = (k (τ (σ (M.op (M.op X2 X2) X0))) X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ (M.op (M.op X2 X2) X0)) X1
       have i₂ := eq1682 (σ X1) X0 X2
       grind)
    | exact superpose eq1682 eq23
    | (have j1 := eq1682 (σ X1) X0 X2
       grind)
    | exact resolve eq23 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq17937 : ∀ X0 X1 X2 : G, (τ (k (σ X0) (σ X1))) = (k (M.op (M.op X2 X2) X0) X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17922 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X2 X2) X0)
       grind)
    | exact superpose eq10 eq17922
    | (have j0 := eq17922 X0 X1 X2
       grind)
    | exact resolve eq17922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17922
  have eq18019 : ∀ X0 X1 X2 : G, (k (τ (σ X0)) X1) = (k (M.op (M.op X2 X2) X0) X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17937 X0 X1 X2
       have i₂ := eq23 (σ X0) X1
       grind)
    | exact superpose eq23 eq17937
    | (have j0 := eq17937 X0 X1 X2
       grind)
    | exact resolve eq17937 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17937
  have eq18066 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op (M.op X2 X2) X0) X1) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18019 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18019
    | (have j0 := eq18019 X0 X1 X2
       grind)
    | exact resolve eq18019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18019
  have eq18079 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (k (M.op (M.op X2 X2) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18066 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq18066
    | (have j0 := eq18066 X0 X1 X2
       grind)
    | exact resolve eq18066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18066
  have eq18092 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op (M.op X2 X2) X0) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq254 eq18079
    | (have j0 := eq18079 X0 X1 X2
       have j1 := eq254 X0 X1
       grind)
    | exact resolve eq18079 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18079
  have eq18155 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op (σ (M.op X0 X0)) X2) X1) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18092 X2 X1 (σ (M.op X0 X0))
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq18092
    | (have j0 := eq18092 X2 X1 X2
       grind)
    | exact resolve eq18092 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18158 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (M.op (τ (M.op X0 X0)) X2) X1) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18092 X2 X1 (τ (M.op X0 X0))
       have i₂ := eq3793 X0
       grind)
    | exact superpose eq3793 eq18092
    | (have j0 := eq18092 X2 X1 X2
       grind)
    | exact resolve eq18092 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18494 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18155 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq18155
    | exact resolve eq18155 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18155
  have eq18798 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) X1) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18158 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq3793 X0
       grind)
    | exact superpose eq3793 eq18158
    | exact resolve eq18158 eq3793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18158
  have eq29910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq465 x y
       grind)
    | exact superpose eq465 eq16
    | (have j1 := eq465 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq465 x y
       grind)
    | exact resolve eq16 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq30066 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq29910
  have eq30155 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq485 y y
       have i₂ := eq30066
       grind)
    | exact superpose eq30066 eq485
    | exact resolve eq485 eq30066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq30190 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3793 (σ y)
       have i₂ := eq30066
       grind)
    | exact superpose eq30066 eq3793
    | exact resolve eq3793 eq30066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq30271 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq30066
       grind)
    | exact superpose eq30066 eq12
    | exact resolve eq12 eq30066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30286 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30271
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq30271
    | exact resolve eq30271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30271
  have eq30329 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq30190
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30190
    | exact resolve eq30190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30190
  have eq30334 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30155
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30155
    | exact resolve eq30155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30155
  have eq30463 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 y y
       have i₂ := eq30329
       grind)
    | exact superpose eq30329 eq66
    | exact resolve eq66 eq30329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq30329
  have eq30472 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq30463
  have eq30473 : x = (M.op x x) := by
    first
    | (have j1 := eq3797 x
       grind)
    | (have r₁ := eq30472
       have r₂ := eq3797 x
       grind)
    | exact resolve eq30472 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797 eq30472
  have eq30478 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq492 x
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq492
    | exact resolve eq492 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30480 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq559 x X0 X1
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq559
    | exact resolve eq559 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq30481 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq560 x X0 X1
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq560
    | exact resolve eq560 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq30510 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X1 (M.op (M.op X0 (τ x)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3854 x X0 X1 X2
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq3854
    | exact resolve eq3854 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq30576 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op x X1) X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18092 X1 X0 x
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq18092
    | (have j0 := eq18092 X1 X0 x
       grind)
    | exact resolve eq18092 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18092
  have eq30583 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq18494 x x
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq18494
    | exact resolve eq18494 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494
  have eq30743 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (k (τ (σ x)) X0) ∨ (τ (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18798 (σ x) x
       have i₂ := eq30478
       grind)
    | exact superpose eq30478 eq18798
    | exact resolve eq18798 eq30478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18798
  have eq30769 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (τ (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq30743 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30743
    | (have j0 := eq30743 X0
       grind)
    | exact resolve eq30743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30743
  have eq30813 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq30769 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30769
    | (have j0 := eq30769 X0
       grind)
    | exact resolve eq30769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30769
  have eq32676 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op (σ x) X1)) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (σ x) X1)
       have i₂ := eq30480 X0 X1
       grind)
    | exact superpose eq30480 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq30480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30480
  have eq34944 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq255 x X0
       have i₂ := eq30813 X0
       grind)
    | exact superpose eq30813 eq255
    | (have j0 := eq255 x X0
       have j1 := eq30813 X0
       grind)
    | exact resolve eq255 eq30813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34954 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ (σ X0) = (σ x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq34944 X0
       have i₂ := eq30478
       grind)
    | exact superpose eq30478 eq34944
    | (have j0 := eq34944 X0
       grind)
    | exact resolve eq34944 eq30478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34944
  have eq63770 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (τ x)) X1)) = (k (M.op (M.op X0 x) X1) X2) ∨ (M.op (M.op (M.op X0 (τ x)) X1) (M.op (M.op X0 (τ x)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30576 X2 (M.op (M.op X0 (τ x)) X1)
       have i₂ := eq30510 X0 x X1
       grind)
    | exact superpose eq30510 eq30576
    | (have j0 := eq30576 X2 (M.op (M.op X0 (τ x)) X1)
       grind)
    | exact resolve eq30576 eq30510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30576
  have eq63948 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (k (M.op (M.op X0 x) X1) X2) ∨ (M.op (M.op (M.op X0 (τ x)) X1) (M.op (M.op X0 (τ x)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63770 X0 X1 X2
       have i₂ := eq30510 X0 X2 X1
       grind)
    | exact superpose eq30510 eq63770
    | (have j0 := eq63770 X0 X1 X2
       grind)
    | exact resolve eq63770 eq30510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30510 eq63770
  have eq64013 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (k (M.op (M.op X0 x) X1) X2) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63948 X0 X1 X2
       have i₂ := eq9 X1 X1 (M.op X0 (τ x))
       grind)
    | exact superpose eq9 eq63948
    | (have j0 := eq63948 X0 X1 X2
       grind)
    | exact resolve eq63948 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63948
  have eq75640 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq254 y y
       have i₂ := eq30334
       grind)
    | exact superpose eq30334 eq254
    | (have j0 := eq254 y x
       grind)
    | exact resolve eq254 eq30334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30334
  have eq75641 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq75640
  have eq75648 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq492 y
       have i₂ := eq75641
       grind)
    | exact superpose eq75641 eq492
    | exact resolve eq492 eq75641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq75641
  have eq75850 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30066 eq75648
    | exact resolve eq75648 eq30066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30066 eq75648
  have eq75851 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq75850
  have eq122584 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30286
       have r₂ := eq75851
       grind)
    | exact resolve eq30286 eq75851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30286 eq75851
  have eq122590 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq122584
       grind)
    | exact superpose eq122584 eq10
    | exact resolve eq10 eq122584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122584
  have eq122728 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq122590
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122590
    | exact resolve eq122590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122590
  have eq122753 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq254 y y
       have i₂ := eq122728
       grind)
    | exact superpose eq122728 eq254
    | (have j0 := eq254 y x
       grind)
    | exact resolve eq254 eq122728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122754 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq122753
  have eq122986 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq122754
       grind)
    | exact superpose eq122754 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq122754
       grind)
    | exact resolve eq12 eq122754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123019 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq122754
  have eq123027 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq122986
  have eq123034 : x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq122728 eq123027
    | exact resolve eq123027 eq122728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122728 eq123027
  have eq123125 : x = (M.op y y) := by
    first
    | (have r₁ := eq123034
       have r₂ := eq123019
       grind)
    | exact resolve eq123034 eq123019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123019 eq123034
  have eq123382 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq9
    | exact resolve eq9 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123383 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq9
    | exact resolve eq9 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123384 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq12
    | exact resolve eq12 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123524 : ∀ X0 : G, x ≠ (M.op y X0) ∨ (M.op (M.op y X0) x) = (k x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq12 x (M.op y X0)
       have i₂ := eq123382 X0
       grind)
    | exact superpose eq123382 eq12
    | (have j0 := eq12 x (M.op y X0)
       grind)
    | exact resolve eq12 eq123382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123382
  have eq123574 : ∀ X0 : G, (M.op (M.op y X0) x) = (k x (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq123524 X0
       have j1 := eq30813 (M.op y X0)
       grind)
    | (have r₁ := eq123524 X0
       have r₂ := eq30813 (M.op y X0)
       grind)
    | exact resolve eq123524 eq30813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30813 eq123524
  have eq123938 : ∀ X0 : G, (M.op X0 y) = (k x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq123574 X0
       have i₂ := eq123383 X0
       grind)
    | exact superpose eq123383 eq123574
    | exact resolve eq123574 eq123383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123574
  have eq169516 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | exact superpose eq13827 eq13805
    | (have j0 := eq13805 X0
       have j1 := eq13827 X0 x x
       grind)
    | exact resolve eq13805 eq13827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13805 eq13827
  have eq169517 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | exact superpose eq69 eq169516
    | (have j0 := eq169516 X0
       have j1 := eq69 X0
       grind)
    | exact resolve eq169516 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq169516
  have eq169972 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq169517 X0
       grind)
    | exact superpose eq169517 eq18
    | (have j1 := eq169517 X0
       grind)
    | exact resolve eq18 eq169517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq169517
  have eq169980 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq169972 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169972
    | (have j0 := eq169972 X0
       grind)
    | exact resolve eq169972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169972
  have eq169981 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq169980 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169980
  have eq170055 : ∀ X0 : G, (k X0 (k X0 (σ (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq169981 X0
       have i₂ := eq271 (τ X0) X0
       grind)
    | exact superpose eq271 eq169981
    | (have j1 := eq271 (τ X0) X0
       grind)
    | exact resolve eq169981 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq170056 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq169981 X0
       have i₂ := eq254 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact superpose eq254 eq169981
    | (have j1 := eq254 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq169981 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170126 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq169981 (σ X0)
       grind)
    | exact superpose eq169981 eq29
    | exact resolve eq29 eq169981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq170240 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq170126 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq170126
    | exact resolve eq170126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170126
  have eq170267 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq170055 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq170055
    | (have j0 := eq170055 X0
       grind)
    | exact resolve eq170055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170055
  have eq170320 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq170240 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq170240
    | exact resolve eq170240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170240
  have eq170462 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq170320 (M.op X1 X0)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq170320
    | exact resolve eq170320 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170320
  have eq246009 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32676 X0 X1
       have i₂ := eq30481 X1 X0
       grind)
    | exact superpose eq30481 eq32676
    | (have j0 := eq32676 X0 X1
       grind)
    | (have r₁ := eq32676 (M.op (σ x) (σ x)) (σ x)
       have r₂ := eq30481 (σ x) (σ x)
       grind)
    | exact resolve eq32676 eq30481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30481 eq32676
  have eq264357 : ∀ X0 : G, (M.op (M.op y X0) x) = (k (M.op x y) X0) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq64013 y x X0
       have i₂ := eq123383 x
       grind)
    | exact superpose eq123383 eq64013
    | (have j0 := eq64013 X0 x X0
       grind)
    | exact resolve eq64013 eq123383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64013
  have eq264870 : ∀ X0 : G, (M.op X0 y) = (k (M.op x y) X0) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq264357 X0
       have i₂ := eq123383 X0
       grind)
    | exact superpose eq123383 eq264357
    | (have j0 := eq264357 X0
       grind)
    | exact resolve eq264357 eq123383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123383 eq264357
  have eq265166 : ∀ X0 : G, (M.op X0 y) = (k (M.op x y) X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq264870 X0
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq264870
    | (have j0 := eq264870 X0
       grind)
    | exact resolve eq264870 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264870
  have eq265736 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op x y)
       have i₂ := eq265166 (τ X0)
       grind)
    | exact superpose eq265166 eq19
    | (have j1 := eq265166 (τ X0)
       grind)
    | exact resolve eq19 eq265166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq266484 : ∀ X0 X1 : G, (k (σ (M.op (τ (σ X0)) y)) (σ X1)) = (σ (M.op X1 (k (τ (σ (M.op x y))) X0))) ∨ (M.op (k (τ (σ (M.op x y))) X0) (k (τ (σ (M.op x y))) X0)) = X1 ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq275 X1 (σ (M.op x y)) X0
       have i₂ := eq265736 (σ X0)
       grind)
    | exact superpose eq265736 eq275
    | (have j0 := eq275 X1 (σ (M.op x y)) X0
       have j1 := eq265736 (σ X0)
       grind)
    | exact resolve eq275 eq265736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq265736
  have eq266543 : ∀ X0 X1 : G, (k (σ (M.op (τ (σ X0)) y)) (σ X1)) = (σ (M.op X1 (k (M.op x y) X0))) ∨ (M.op (k (τ (σ (M.op x y))) X0) (k (τ (σ (M.op x y))) X0)) = X1 ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq266484 X0 X1
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq266484
    | (have j0 := eq266484 X0 X1
       grind)
    | exact resolve eq266484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266484
  have eq266674 : ∀ X0 X1 : G, (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op (τ (σ X0)) y) X1)) ∨ (M.op (k (τ (σ (M.op x y))) X0) (k (τ (σ (M.op x y))) X0)) = X1 ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq266543 X0 X1
       have i₂ := eq15 (M.op (τ (σ X0)) y) X1
       grind)
    | exact superpose eq15 eq266543
    | (have j0 := eq266543 X0 X1
       grind)
    | exact resolve eq266543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266543
  have eq266793 : ∀ X0 X1 : G, (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) ∨ (M.op (k (τ (σ (M.op x y))) X0) (k (τ (σ (M.op x y))) X0)) = X1 ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq266674 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266674
    | (have j0 := eq266674 X0 X1
       grind)
    | exact resolve eq266674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266674
  have eq266868 : ∀ X0 X1 : G, (M.op (k (M.op x y) X0) (k (M.op x y) X0)) = X1 ∨ (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) ∨ (τ (σ X0)) = x := by
    intro X0 X1
    first
    | (have i₁ := eq266793 X0 X1
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq266793
    | (have j0 := eq266793 X0 X1
       grind)
    | exact resolve eq266793 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266793
  have eq266918 : ∀ X0 X1 : G, x = X0 ∨ (M.op (k (M.op x y) X0) (k (M.op x y) X0)) = X1 ∨ (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266868 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266868
    | (have j0 := eq266868 X0 X1
       grind)
    | exact resolve eq266868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266868
  have eq266942 : ∀ X0 X1 : G, x = X0 ∨ (M.op (M.op X0 y) (M.op X0 y)) = X1 ∨ (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq265166 eq266918
    | (have j0 := eq266918 X0 X1
       have j1 := eq265166 X0
       grind)
    | exact resolve eq266918 eq265166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266918
  have eq266948 : ∀ X0 X1 : G, (M.op y y) = X1 ∨ x = X0 ∨ (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266942 X0 X1
       have i₂ := eq9 y y X0
       grind)
    | exact superpose eq9 eq266942
    | (have j0 := eq266942 X0 X1
       grind)
    | exact resolve eq266942 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266942
  have eq266953 : ∀ X0 X1 : G, x = X1 ∨ x = X0 ∨ (σ (M.op X1 (k (M.op x y) X0))) = (σ (k (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq266948 X0 X1
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq266948
    | (have j0 := eq266948 X0 X1
       grind)
    | exact resolve eq266948 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266948
  have eq266956 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 y))) = (σ (k (M.op X0 y) X1)) ∨ x = X0 ∨ x = X1 := by
    intro X0 X1
    first
    | exact superpose eq265166 eq266953
    | (have j0 := eq266953 X0 X0
       have j1 := eq265166 X0
       grind)
    | exact resolve eq266953 eq265166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265166 eq266953
  have eq271502 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq170056 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170056
  have eq684638 : ∀ X0 X1 : G, (k (M.op X1 y) X0) = (τ (σ (M.op X0 (M.op X1 y)))) ∨ x = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op X1 y) X0)
       have i₂ := eq266956 X1 X0
       grind)
    | exact superpose eq266956 eq10
    | (have j1 := eq266956 X1 X1
       grind)
    | exact resolve eq10 eq266956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266956
  have eq685233 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (k (M.op X1 y) X0) ∨ x = X1 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq684638 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X1 y))
       grind)
    | exact superpose eq10 eq684638
    | (have j0 := eq684638 X1 X1
       grind)
    | exact resolve eq684638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684638
  have eq685488 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (σ (M.op (τ y) (τ y))) ∨ x = X0 ∨ (M.op y y) = (σ (M.op (τ y) (τ y))) := by
    intro X0
    first
    | (have i₁ := eq685233 X0 (σ (M.op (τ y) (τ y)))
       have i₂ := eq271502 y
       grind)
    | exact superpose eq271502 eq685233
    | (have j0 := eq685233 (σ (M.op (τ y) (τ y))) (σ (M.op (τ y) (τ y)))
       have j1 := eq271502 y
       grind)
    | exact resolve eq685233 eq271502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271502
  have eq686114 : ∀ X0 : G, x = (σ (M.op (τ y) (τ y))) ∨ (M.op X0 y) = (k y X0) ∨ x = (σ (M.op (τ y) (τ y))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq685488 X0
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq685488
    | (have j0 := eq685488 X0
       grind)
    | exact resolve eq685488 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685488
  have eq686115 : ∀ X0 : G, x = (σ (M.op (τ y) (τ y))) ∨ (M.op X0 y) = (k y X0) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq686114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686114
  have eq686959 : x ≠ x ∨ (M.op (σ (M.op (τ y) (τ y))) y) = (k y (σ (M.op (τ y) (τ y)))) ∨ x = (σ (M.op (τ y) (τ y))) := by
    first
    | (have j0 := eq686115 (σ (M.op (τ y) (τ y)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686115
  have eq686960 : (M.op (σ (M.op (τ y) (τ y))) y) = (k y (σ (M.op (τ y) (τ y)))) ∨ x = (σ (M.op (τ y) (τ y))) := by grind
  clear eq686959
  have eq686962 : y = (M.op (σ (M.op (τ y) (τ y))) y) ∨ x = (σ (M.op (τ y) (τ y))) := by
    first
    | (have i₁ := eq686960
       have i₂ := eq169981 y
       grind)
    | exact superpose eq169981 eq686960
    | exact resolve eq686960 eq169981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169981 eq686960
  have eq688070 : y = (M.op (σ (τ y)) y) ∨ x = (σ (τ y)) ∨ y = (k y (k y y)) := by
    first
    | (have i₁ := eq686962
       have i₂ := eq170267 y
       grind)
    | exact superpose eq170267 eq686962
    | (have j1 := eq170267 y
       grind)
    | exact resolve eq686962 eq170267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170267 eq686962
  have eq688246 : y = (M.op y y) ∨ x = (σ (τ y)) ∨ y = (k y (k y y)) := by
    first
    | (have i₁ := eq688070
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq688070
    | exact resolve eq688070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688070
  have eq688274 : x = y ∨ x = (σ (τ y)) ∨ y = (k y (k y y)) := by
    first
    | (have i₁ := eq688246
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq688246
    | exact resolve eq688246 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688246
  have eq688278 : x = y ∨ x = y ∨ y = (k y (k y y)) := by
    first
    | (have i₁ := eq688274
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq688274
    | exact resolve eq688274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688274
  have eq688279 : y = (k y (k y y)) ∨ x = y := by grind
  clear eq688278
  have eq688285 : y = (M.op (k y y) y) ∨ (M.op y y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq254 y (k y y)
       have i₂ := eq688279
       grind)
    | exact superpose eq688279 eq254
    | (have j0 := eq254 y y
       grind)
    | exact resolve eq254 eq688279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq688279
  have eq688301 : x = (k y y) ∨ y = (M.op (k y y) y) ∨ x = y := by
    first
    | (have i₁ := eq688285
       have i₂ := eq123125
       grind)
    | exact superpose eq123125 eq688285
    | exact resolve eq688285 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688285
  have eq688303 : y = (M.op (k y y) y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq688301
       have r₂ := eq123384
       grind)
    | exact resolve eq688301 eq123384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688301
  have eq688327 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (k y y) ∨ x = X0 ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq685233 X0 (k y y)
       have i₂ := eq688303
       grind)
    | exact superpose eq688303 eq685233
    | (have j0 := eq685233 (k y y) (k y y)
       grind)
    | exact resolve eq685233 eq688303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685233 eq688303
  have eq688408 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (k y y) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq688327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688327
  have eq688702 : x ≠ (M.op y y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have j0 := eq688408 (k y y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688408
  have eq688716 : x ≠ (M.op y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq688702
       have r₂ := eq123384
       grind)
    | exact resolve eq688702 eq123384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123384 eq688702
  have eq688828 : x = (k y y) := by
    first
    | (have r₁ := eq688716
       have r₂ := eq123125
       grind)
    | exact resolve eq688716 eq123125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123125 eq688716
  have eq689030 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq255 y y
       have i₂ := eq688828
       grind)
    | exact superpose eq688828 eq255
    | (have j0 := eq255 y y
       grind)
    | exact resolve eq255 eq688828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq689539 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq170462 (σ y) (σ y)
       have i₂ := eq689030
       grind)
    | exact superpose eq689030 eq170462
    | exact resolve eq170462 eq689030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170462
  have eq689548 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq689030
  have eq689568 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq689539
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq689539
    | exact resolve eq689539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689539
  have eq689775 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq689568
       have i₂ := eq688828
       grind)
    | exact superpose eq688828 eq689568
    | exact resolve eq689568 eq688828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688828 eq689568
  have eq689816 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq689775
       have r₂ := eq689548
       grind)
    | exact resolve eq689775 eq689548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689548 eq689775
  have eq690332 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ y)
       have i₂ := eq689816
       grind)
    | exact superpose eq689816 eq9
    | exact resolve eq9 eq689816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690333 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq689816
       grind)
    | exact superpose eq689816 eq9
    | exact resolve eq9 eq689816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689816
  have eq692926 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ (M.op (M.op (σ y) X0) (σ x)) = (k (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq246009 (σ x) (M.op (σ y) X0)
       have i₂ := eq690332 X0
       grind)
    | exact superpose eq690332 eq246009
    | exact resolve eq246009 eq690332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246009 eq690332
  have eq692932 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ x)) = (k (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq692926 X0
       have j1 := eq30583 (M.op (σ y) X0)
       grind)
    | (have r₁ := eq692926 X0
       have r₂ := eq30583 (M.op (σ y) X0)
       grind)
    | exact resolve eq692926 eq30583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30583 eq692926
  have eq694074 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq692932 X0
       have i₂ := eq690333 X0
       grind)
    | exact superpose eq690333 eq692932
    | exact resolve eq692932 eq690333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690333 eq692932
  have eq694080 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op y x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq694074 (σ x)
       have i₂ := eq34954 y
       grind)
    | exact superpose eq34954 eq694074
    | (have j1 := eq34954 y
       grind)
    | exact resolve eq694074 eq34954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954 eq694074
  have eq694351 : (M.op (σ x) (σ y)) = (σ (k x (M.op y x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq694080
       have i₂ := eq15 x (M.op y x)
       grind)
    | exact superpose eq15 eq694080
    | exact resolve eq694080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694080
  have eq694398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq694351
       have i₂ := eq123938 x
       grind)
    | exact superpose eq123938 eq694351
    | exact resolve eq694351 eq123938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123938 eq694351
  have eq694415 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq694398
       have r₂ := eq16
       grind)
    | exact resolve eq694398 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694398
  have eq694427 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq694415
       grind)
    | exact superpose eq694415 eq10
    | exact resolve eq10 eq694415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694415
  have eq695079 : x = y ∨ x = y := by
    first
    | (have i₁ := eq694427
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq694427
    | exact resolve eq694427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694427
  have eq695080 : x = y := by grind
  clear eq695079
  have eq695147 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq695080
       grind)
    | exact superpose eq695080 eq16
    | exact resolve eq16 eq695080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695080
  have eq695282 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq695147
       have i₂ := eq30473
       grind)
    | exact superpose eq30473 eq695147
    | exact resolve eq695147 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30473 eq695147
  have eq695290 : False := by grind
  exact eq695290

/-- `Equation3866`: `x ◇ x = (x ◇ (x ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_x_pxy_Equation3866 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3866 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3866.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op x x) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) x X3
       have i₂ := eq14 X0 X1 (M.op (M.op X0 (M.op X0 X1)) x)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq53 X0 x X3
       have i₂ := eq14 X0 x (M.op X0 (M.op X0 x))
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq98 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) x
       have r₂ := eq54 X0 x
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq301 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq441 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq301
    | (have j0 := eq301 X0 (M.op x y)
       grind)
    | exact resolve eq301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq505 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq160 eq441
    | exact resolve eq441 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq672 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq12 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq679 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq683 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq673 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq673 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq673 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq684 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq682 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq693 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq694 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | exact resolve eq684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq2998 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq679 (M.op X0 X0)
       have i₂ := eq236 X0 (M.op X0 X0)
       grind)
    | exact superpose eq236 eq679
    | (have j0 := eq679 (M.op X0 X0)
       grind)
    | exact resolve eq679 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3003 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq679 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq679
    | (have j0 := eq679 (τ X0)
       grind)
    | exact resolve eq679 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq679
  have eq3012 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3003
    | (have j0 := eq3003 X0
       grind)
    | exact resolve eq3003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3015 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2998 X0
       have i₂ := eq54 X0 (M.op X0 X0)
       grind)
    | exact superpose eq54 eq2998
    | (have j0 := eq2998 X0
       grind)
    | exact resolve eq2998 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3016 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq3015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3020 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3012 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3012
    | (have j0 := eq3012 X0
       grind)
    | exact resolve eq3012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq3761 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq97 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 x
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq3771 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3761
  have eq3776 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3771
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3771
    | exact resolve eq3771 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3794 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3776
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3776 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3802 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3794 eq49
    | exact resolve eq49 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3958 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98
    | (have j0 := eq98 y
       grind)
    | exact resolve eq98 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3967 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3958
  have eq3971 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3967
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq3967
    | exact resolve eq3967 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3967
  have eq3996 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3971
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3971 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971
  have eq4028 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3996 eq90
    | exact resolve eq90 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3996
  have eq4326 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq138
    | (have j0 := eq138 (M.op x y)
       grind)
    | exact resolve eq138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq4334 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4326
  have eq4337 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq137 eq4334
    | exact resolve eq4334 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq4334
  have eq4369 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4337
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4337 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4427 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq4369 eq160
    | exact resolve eq160 eq4369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq5498 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq4369 eq505
    | exact resolve eq505 eq4369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq4369
  have eq5499 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq5498
       have i₂ := eq236 sF1 sF1
       grind)
    | exact superpose eq236 eq5498
    | exact resolve eq5498 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq5498
  have eq13832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13839 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13832
    | exact resolve eq13832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13832
  have eq13850 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq13839
       have r₂ := eq27
       grind)
    | exact resolve eq13839 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13839
  have eq13852 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13850
    | exact resolve eq13850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13850
  have eq13856 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13852 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13852
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13852
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13852
       grind)
    | exact resolve eq12 eq13852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13852
  have eq13860 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13856
  have eq13864 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq13860
    | exact resolve eq13860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13860
  have eq13865 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq13864
  have eq14032 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13865 eq60
    | exact resolve eq60 eq13865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq13865
  have eq14062 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq14032
    | exact resolve eq14032 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14032
  have eq14827 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14062
       grind)
    | exact superpose eq14062 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14062
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14062
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14062
       grind)
    | exact resolve eq12 eq14062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14062
  have eq14831 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14827
  have eq14832 : x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14831
  have eq14836 : x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14832
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14832
    | exact resolve eq14832 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14832
  have eq14837 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14836
  have eq14847 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq14837
       grind)
    | exact superpose eq14837 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14850 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq678 x y
       have i₂ := eq14837
       grind)
    | exact superpose eq14837 eq678
    | (have j0 := eq678 x y
       grind)
    | exact resolve eq678 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14852 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq694 x y
       have i₂ := eq14837
       grind)
    | exact superpose eq14837 eq694
    | (have j0 := eq694 x y
       grind)
    | exact resolve eq694 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq14837
  have eq14855 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14852
  have eq14857 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14850
  have eq14859 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14847
  have eq14861 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14855
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq14855
    | exact resolve eq14855 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14855
  have eq14863 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14857
    | exact resolve eq14857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14857
  have eq14864 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14859
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14859
    | exact resolve eq14859 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14859
  have eq14865 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14864
  have eq14875 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14861
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14861
    | exact resolve eq14861 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14861
  have eq14877 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14863
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14863
    | exact resolve eq14863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14863
  have eq14880 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14875
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14875
    | exact resolve eq14875 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14875
  have eq14882 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14877
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14877
    | exact resolve eq14877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877
  have eq14883 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14880
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14880
    | exact resolve eq14880 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14880
  have eq14885 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14882
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14882
    | exact resolve eq14882 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq14886 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14883
       have r₂ := eq79
       grind)
    | exact resolve eq14883 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq14883
  have eq14887 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14885
    | exact resolve eq14885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14885
  have eq14888 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14887
  have eq14892 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq14865
       grind)
    | exact superpose eq14865 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14865
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14865
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14865
       grind)
    | exact resolve eq13 eq14865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14865
  have eq14894 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14892
  have eq14898 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14894
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14894
    | exact resolve eq14894 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14894
  have eq14949 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14888 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14888
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14888
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14888
       grind)
    | exact resolve eq13 eq14888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq14951 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14949
  have eq14956 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14951
    | exact resolve eq14951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14951
  have eq14958 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq14898
       grind)
    | exact superpose eq14898 eq75
    | exact resolve eq75 eq14898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14898
  have eq14984 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14958
    | exact resolve eq14958 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14958
  have eq15072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14984 eq14956
    | exact resolve eq14956 eq14984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14956 eq14984
  have eq15080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15072
  have eq15086 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15080
       have r₂ := eq27
       grind)
    | exact resolve eq15080 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15080
  have eq15097 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15086 eq27
    | exact resolve eq27 eq15086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15099 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15086 eq67
    | (have r₁ := eq67
       have r₂ := eq15086
       grind)
    | exact resolve eq67 eq15086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq15106 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15099
  have eq15116 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15106 eq119
    | exact resolve eq119 eq15106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq15136 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15116
  have eq15195 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14886 eq85
    | exact resolve eq85 eq14886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14886
  have eq15239 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq15195
    | exact resolve eq15195 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15249 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15239 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15239
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15239
       grind)
    | exact resolve eq13 eq15239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15251 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq15249
  have eq15257 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15251
    | exact resolve eq15251 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq15268 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15257 eq85
    | exact resolve eq85 eq15257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq15303 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15136 eq15239
    | exact resolve eq15239 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15136 eq15239
  have eq15309 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15303
  have eq15321 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15309
       have r₂ := eq78
       grind)
    | exact resolve eq15309 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15309
  have eq15399 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15321
       grind)
    | exact superpose eq15321 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15321
  have eq15411 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15399
  have eq15416 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15411
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15411
    | exact resolve eq15411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15411
  have eq15444 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15416
       grind)
    | exact superpose eq15416 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15416
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15416
       grind)
    | exact resolve eq13 eq15416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15416
  have eq15446 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15444
  have eq15450 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15446
    | exact resolve eq15446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15446
  have eq15457 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq15450
       grind)
    | exact superpose eq15450 eq75
    | exact resolve eq75 eq15450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15489 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq15457
    | exact resolve eq15457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15457
  have eq15577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15489 eq15257
    | exact resolve eq15257 eq15489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15257 eq15489
  have eq15585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15577
  have eq15596 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq15585
       have r₂ := eq27
       grind)
    | exact resolve eq15585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585
  have eq15695 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15450
       have i₂ := eq15596
       grind)
    | exact superpose eq15596 eq15450
    | exact resolve eq15450 eq15596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15450 eq15596
  have eq15709 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15695
  have eq15739 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15709 eq29
    | exact resolve eq29 eq15709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15709
  have eq15909 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq15739
    | exact resolve eq15739 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15739
  have eq15910 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15909
  have eq15926 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15910 eq20
    | exact resolve eq20 eq15910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15928 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15910 eq50
    | exact resolve eq50 eq15910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq15982 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq16036 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15928 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15928
    | (have j0 := eq15928 X0
       grind)
    | exact resolve eq15928 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928
  have eq16038 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15926
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15926
    | exact resolve eq15926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926
  have eq16517 : ∀ X0 : G, (M.op x x) = (M.op y X0) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15910 eq16036
    | exact resolve eq16036 eq15910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15910 eq16036
  have eq16534 : ∀ X0 : G, (M.op x x) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16517 X0
       grind)
    | (have r₁ := eq16517 X0
       have r₂ := eq15982
       grind)
    | exact resolve eq16517 eq15982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982 eq16517
  have eq48405 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15268
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq15268
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq15268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15268
  have eq48445 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq48405
  have eq48470 : x = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48445
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48445
    | exact resolve eq48445 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48445
  have eq48471 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq48470
  have eq48521 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16534 x
       have i₂ := eq48471
       grind)
    | exact superpose eq48471 eq16534
    | exact resolve eq16534 eq48471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48471
  have eq48528 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq48521
  have eq98778 : (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3016 x
       have i₂ := eq48528
       grind)
    | exact superpose eq48528 eq3016
    | exact resolve eq3016 eq48528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48528
  have eq98790 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98778
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq98778
    | exact resolve eq98778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98778
  have eq98800 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15086 eq98790
    | exact resolve eq98790 eq15086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15086 eq98790
  have eq98826 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq98800
  have eq99557 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq98826 eq3802
    | exact resolve eq3802 eq98826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802 eq98826
  have eq99596 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq99557
    | exact resolve eq99557 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq99557
  have eq100319 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16534 x
       have i₂ := eq99596
       grind)
    | exact superpose eq99596 eq16534
    | exact resolve eq16534 eq99596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16534
  have eq100322 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq99596
       grind)
    | exact superpose eq99596 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq99596
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq99596
       grind)
    | exact resolve eq12 eq99596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99596
  have eq100326 : x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq100322
  have eq100329 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq100319
  have eq100333 : x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq100326
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100326
    | exact resolve eq100326 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100326
  have eq100334 : x = (k x y) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq100333
  have eq100354 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq3016 x
       have i₂ := eq100329
       grind)
    | exact superpose eq100329 eq3016
    | exact resolve eq3016 eq100329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016 eq100329
  have eq100372 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq100354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100354
    | exact resolve eq100354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100354
  have eq101246 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq100334
       grind)
    | exact superpose eq100334 eq44
    | exact resolve eq44 eq100334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100334
  have eq101302 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq101246
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101246
    | exact resolve eq101246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101246
  have eq102196 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq100372 eq54
    | exact resolve eq54 eq100372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100372
  have eq104067 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq101302 eq15106
    | exact resolve eq15106 eq101302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15106 eq101302
  have eq104141 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq104067
  have eq111016 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq104141 eq102196
    | exact resolve eq102196 eq104141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102196 eq104141
  have eq111022 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq111016
  have eq111079 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq111022
       grind)
    | exact superpose eq111022 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq111022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111022
  have eq111094 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq111079
  have eq111136 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq54 x x
       have i₂ := eq111094
       grind)
    | exact superpose eq111094 eq54
    | exact resolve eq54 eq111094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111094
  have eq112773 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq111136 y
       grind)
    | exact superpose eq111136 eq18
    | (have j1 := eq111136 y
       grind)
    | exact resolve eq18 eq111136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111136
  have eq112807 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq112773
  have eq112967 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq112807 eq16038
    | exact resolve eq16038 eq112807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16038 eq112807
  have eq113263 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq112967
  have eq113338 : x = (M.op x y) := by
    first
    | (have r₁ := eq113263
       have r₂ := eq15097
       grind)
    | exact resolve eq113263 eq15097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15097 eq113263
  have eq114169 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq113338 eq20
    | exact resolve eq20 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114173 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq113338 eq66
    | (have r₁ := eq66
       have r₂ := eq113338
       grind)
    | exact resolve eq66 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq114176 : x ≠ x ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq113338 eq78
    | (have r₁ := eq78
       have r₂ := eq113338
       grind)
    | exact resolve eq78 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq114309 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq114176
  have eq114310 : (k x y) = (M.op y x) := by grind
  clear eq114173
  have eq114438 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114169
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq114169
    | exact resolve eq114169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114169
  have eq114495 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq114438 eq26
    | exact resolve eq26 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114500 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq114438 eq51
    | exact resolve eq51 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq114848 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq114310
       grind)
    | exact superpose eq114310 eq44
    | exact resolve eq44 eq114310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq114310
  have eq114898 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq114438 eq114848
    | exact resolve eq114848 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114848
  have eq121682 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq678 y x
       have i₂ := eq114309
       grind)
    | exact superpose eq114309 eq678
    | (have j0 := eq678 y x
       grind)
    | exact resolve eq678 eq114309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq121683 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq693 y x
       have i₂ := eq114309
       grind)
    | exact superpose eq114309 eq693
    | (have j0 := eq693 y x
       grind)
    | exact resolve eq693 eq114309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq114309
  have eq121688 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq121683
  have eq121689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq121682
  have eq121696 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121688
    | exact resolve eq121688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121688
  have eq121697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121689
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121689
    | exact resolve eq121689 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121689
  have eq121715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121696
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121696
    | exact resolve eq121696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121696
  have eq121716 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121697
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121697
    | exact resolve eq121697 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121697
  have eq121731 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq121715
    | exact resolve eq121715 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121715
  have eq121732 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq121716
    | exact resolve eq121716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121716
  have eq121738 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121731
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121731
    | exact resolve eq121731 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121731
  have eq121739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114438 eq121732
    | exact resolve eq121732 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121732
  have eq121741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121738
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121738
    | exact resolve eq121738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121738
  have eq121742 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq121739
       have r₂ := eq27
       grind)
    | exact resolve eq121739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121739
  have eq121744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq121741
    | exact resolve eq121741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq121741
  have eq121745 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121742
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121742
    | exact resolve eq121742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121742
  have eq121747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114438 eq121744
    | exact resolve eq121744 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121744
  have eq121748 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114438 eq121745
    | exact resolve eq121745 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121745
  have eq121750 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq121747
       have r₂ := eq27
       grind)
    | exact resolve eq121747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121747
  have eq121751 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121748
    | exact resolve eq121748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121748
  have eq123127 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114898
       have i₂ := eq121750
       grind)
    | exact superpose eq121750 eq114898
    | exact resolve eq114898 eq121750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114898
  have eq123132 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq121750
       grind)
    | exact superpose eq121750 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq121750
       grind)
    | exact resolve eq13 eq121750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121750
  have eq123134 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq123132
  have eq123138 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123134
    | exact resolve eq123134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123134
  have eq123140 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq123127
    | exact resolve eq123127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123127
  have eq123141 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113338 eq123138
    | exact resolve eq123138 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123138
  have eq123192 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123140 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq123140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123140
  have eq123203 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114495 eq123192
    | exact resolve eq123192 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123192
  have eq123204 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq123203
  have eq123218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq114495 eq123204
    | exact resolve eq123204 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123204
  have eq123231 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq123218
       have r₂ := eq27
       grind)
    | exact resolve eq123218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123218
  have eq123262 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq123141
       grind)
    | exact superpose eq123141 eq75
    | exact resolve eq75 eq123141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123141
  have eq123338 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114438 eq123262
    | exact resolve eq123262 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123262
  have eq123357 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq123338
    | exact resolve eq123338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123338
  have eq123376 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114438 eq123357
    | exact resolve eq123357 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123357
  have eq124452 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123231 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq123231
       grind)
    | exact resolve eq13 eq123231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123231
  have eq124454 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq124452
  have eq124458 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114495 eq124454
    | exact resolve eq124454 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124454
  have eq125574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq124458 eq123376
    | exact resolve eq123376 eq124458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123376 eq124458
  have eq125600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq125574
  have eq125602 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq125600
       have r₂ := eq27
       grind)
    | exact resolve eq125600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125600
  have eq125617 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq125602 eq27
    | exact resolve eq27 eq125602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125633 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq125602 eq114500
    | exact resolve eq114500 eq125602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114500
  have eq125634 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq114495 eq125633
    | exact resolve eq125633 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125633
  have eq125640 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq125602 eq125634
    | exact resolve eq125634 eq125602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125634
  have eq125727 : (k y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125640 eq4028
    | exact resolve eq4028 eq125640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq125777 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4427 eq125727
    | exact resolve eq125727 eq4427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125727
  have eq125793 : (k x x) = (k y y) := by
    first
    | exact superpose eq113338 eq125777
    | exact resolve eq125777 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125777
  have eq125827 : y ≠ (k x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3020 y
       have i₂ := eq125793
       grind)
    | exact superpose eq125793 eq3020
    | (have j0 := eq3020 y
       grind)
    | exact resolve eq3020 eq125793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq125793
  have eq126163 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq125640 eq121751
    | exact resolve eq121751 eq125640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121751
  have eq126317 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq126163 eq4427
    | exact resolve eq4427 eq126163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126163
  have eq126369 : (τ (σ y)) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq113338 eq126317
    | exact resolve eq126317 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126317
  have eq126379 : y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq126369
    | exact resolve eq126369 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126369
  have eq131193 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq125827
       have i₂ := eq126379
       grind)
    | exact superpose eq126379 eq125827
    | (have r₁ := eq125827
       have r₂ := eq126379
       grind)
    | exact resolve eq125827 eq126379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125827 eq126379
  have eq131199 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq131193
  have eq131202 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq54 y x
       have i₂ := eq131199
       grind)
    | exact superpose eq131199 eq54
    | exact resolve eq54 eq131199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131199
  have eq131251 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq131202 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131202
  have eq131252 : y = (M.op y x) := by grind
  clear eq131251
  have eq131268 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq131252
       grind)
    | exact superpose eq131252 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq131252
       grind)
    | exact resolve eq13 eq131252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131252
  have eq131270 : (M.op x y) = (k y x) := by grind
  clear eq131268
  have eq131274 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq131270
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131270
    | exact resolve eq131270 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq131270
  have eq131277 : x = (k y x) := by
    first
    | exact superpose eq113338 eq131274
    | exact resolve eq131274 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131274
  have eq132720 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq131277
       grind)
    | exact superpose eq131277 eq75
    | exact resolve eq75 eq131277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq132794 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq114438 eq132720
    | exact resolve eq132720 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132720
  have eq132813 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq132794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132794
    | exact resolve eq132794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132794
  have eq132832 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq114438 eq132813
    | exact resolve eq132813 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132813
  have eq132920 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq132832 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq132832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132832
  have eq132932 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq125640 eq132920
    | exact resolve eq132920 eq125640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132920
  have eq132943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq114495 eq132932
    | exact resolve eq132932 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132932
  have eq132954 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq132943
       have r₂ := eq27
       grind)
    | exact resolve eq132943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132943
  have eq132964 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125640 eq132954
    | exact resolve eq132954 eq125640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125640 eq132954
  have eq134835 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132964 eq4427
    | exact resolve eq4427 eq132964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427 eq132964
  have eq134888 : (τ (σ y)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq113338 eq134835
    | exact resolve eq134835 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134835
  have eq134898 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k x x) := by
    first
    | exact superpose eq29 eq134888
    | exact resolve eq134888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134888
  have eq136820 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq134898 eq54
    | exact resolve eq54 eq134898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq134898
  have eq136915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq136820 eq114495
    | exact resolve eq114495 eq136820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136820
  have eq136953 : y = (k x x) := by
    first
    | (have r₁ := eq136915
       have r₂ := eq27
       grind)
    | exact resolve eq136915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq136915
  have eq136993 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq136953
       grind)
    | exact superpose eq136953 eq43
    | exact resolve eq43 eq136953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq137047 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3794 eq136993
    | exact resolve eq136993 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794 eq136993
  have eq137067 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq114438 eq137047
    | exact resolve eq137047 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137047
  have eq137081 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq137067
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq137067
    | exact resolve eq137067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137067
  have eq138777 : (τ (M.op (σ (M.op x y)) (σ y))) = (k (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq137081 eq5499
    | exact resolve eq5499 eq137081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5499 eq137081
  have eq138825 : (k (k x x) x) = (τ (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq113338 eq138777
    | exact resolve eq138777 eq113338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113338 eq138777
  have eq138836 : (τ (M.op (σ x) (σ y))) = (k (k x x) x) := by
    first
    | exact superpose eq114495 eq138825
    | exact resolve eq138825 eq114495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114495 eq138825
  have eq138845 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq138836
       have i₂ := eq136953
       grind)
    | exact superpose eq136953 eq138836
    | exact resolve eq138836 eq136953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136953 eq138836
  have eq138852 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq125602 eq138845
    | exact resolve eq138845 eq125602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125602 eq138845
  have eq138856 : x = (τ (σ y)) := by
    first
    | (have i₁ := eq138852
       have i₂ := eq131277
       grind)
    | exact superpose eq131277 eq138852
    | exact resolve eq138852 eq131277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131277 eq138852
  have eq138860 : x = y := by
    first
    | exact superpose eq29 eq138856
    | exact resolve eq138856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq138856
  have eq140683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq138860
       grind)
    | exact superpose eq138860 eq24
    | exact resolve eq24 eq138860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq138860
  have eq141080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq140683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq140683
    | exact resolve eq140683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq140683
  have eq141215 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq114438 eq141080
    | exact resolve eq141080 eq114438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114438 eq141080
  have eq141307 : False := by grind
  exact eq141307

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq280 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4778 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq279
    | (have j0 := eq279 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4779 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq6368 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq280
  have eq6376 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq6389 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6376 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq6376
    | (have j0 := eq6376 X0
       grind)
    | exact resolve eq6376 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6376
  have eq6738 : ∀ X0 : G, (M.op (τ (σ (k X0 X0))) (τ (σ X0))) = (τ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6389 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6389
    | (have j0 := eq6389 (σ X0)
       grind)
    | exact resolve eq6389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6389
  have eq6806 : ∀ X0 : G, (M.op (τ (σ (k X0 X0))) (τ (σ X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6738 X0
       have i₂ := eq23 (σ (k X0 X0)) X0
       grind)
    | exact superpose eq23 eq6738
    | (have j0 := eq6738 X0
       grind)
    | exact resolve eq6738 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6738
  have eq6825 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6806 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq6806
    | (have j0 := eq6806 X0
       grind)
    | exact resolve eq6806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6806
  have eq6841 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6825 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6825
    | (have j0 := eq6825 X0
       grind)
    | exact resolve eq6825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6857 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6841 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6841
    | (have j0 := eq6841 X0
       grind)
    | exact resolve eq6841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841
  have eq6912 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6857 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6857
    | (have j0 := eq6857 (σ X0)
       grind)
    | exact resolve eq6857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857
  have eq7043 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6912 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq6912
    | (have j0 := eq6912 X0
       grind)
    | exact resolve eq6912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq7171 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7043 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7043
    | (have j0 := eq7043 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq7043 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7043
  have eq7264 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171
  have eq7295 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq7264
  have eq38101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4778 x y
       grind)
    | exact superpose eq4778 eq16
    | (have j1 := eq4778 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4778 x y
       grind)
    | exact resolve eq16 eq4778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778
  have eq38151 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38101
  have eq38344 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38151
  have eq38378 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38344
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq38344
    | exact resolve eq38344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38344
  have eq38412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq38378
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq38378 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38378
  have eq38436 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38412
       have r₂ := eq16
       grind)
    | exact resolve eq38412 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38412
  have eq38440 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38436
       grind)
    | exact superpose eq38436 eq16
    | exact resolve eq16 eq38436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38444 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq38436
       grind)
    | exact superpose eq38436 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq38436
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq38436
       grind)
    | exact resolve eq13 eq38436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38436
  have eq38446 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38444
  have eq38448 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38446
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq38446
    | exact resolve eq38446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38446
  have eq38449 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq38448
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq38448 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38448
  have eq38450 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38449
       have r₂ := eq38440
       grind)
    | exact resolve eq38449 eq38440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38440 eq38449
  have eq38486 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38450
  have eq38521 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38486
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq38486
    | exact resolve eq38486 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38486
  have eq38559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq38521
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq38521 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38521
  have eq38587 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38559
       have r₂ := eq16
       grind)
    | exact resolve eq38559 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38559
  have eq38657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7295 y
       have i₂ := eq38587
       grind)
    | exact superpose eq38587 eq7295
    | (have j0 := eq7295 y
       grind)
    | exact resolve eq7295 eq38587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38666 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38657
       have r₂ := eq16
       grind)
    | exact resolve eq38657 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38657
  have eq38724 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq38666
       grind)
    | exact superpose eq38666 eq64
    | exact resolve eq64 eq38666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38775 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38724
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38724
    | exact resolve eq38724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38724
  have eq38794 : (k y y) = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38666 eq38775
    | exact resolve eq38775 eq38666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38666 eq38775
  have eq38810 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38794
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38794
    | exact resolve eq38794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38794
  have eq38847 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq38810
       grind)
    | exact superpose eq38810 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq38810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38810
  have eq38848 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq38847
  have eq38867 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq38587 eq38848
    | exact resolve eq38848 eq38587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38848
  have eq38868 : x = (M.op x y) ∨ x = y := by grind
  clear eq38867
  have eq38897 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38868 eq38587
    | exact resolve eq38587 eq38868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38587
  have eq38906 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq38868
       grind)
    | exact superpose eq38868 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq38868
       grind)
    | exact resolve eq13 eq38868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38908 : x = (k x y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq38906
  have eq39144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq279 x y
       have i₂ := eq38908
       grind)
    | exact superpose eq38908 eq279
    | (have j0 := eq279 x y
       grind)
    | exact resolve eq279 eq38908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq39147 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq39144
  have eq43332 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq39147
  have eq43378 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq43332
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq43332
    | exact resolve eq43332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43332
  have eq43413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq38908 eq43378
    | exact resolve eq43378 eq38908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38908 eq43378
  have eq43414 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq43413
  have eq43461 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq43414
       grind)
    | exact superpose eq43414 eq16
    | exact resolve eq16 eq43414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43414
  have eq43472 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq38868 eq43461
    | exact resolve eq43461 eq38868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38868 eq43461
  have eq43473 : x = (M.op y y) ∨ x = y := by grind
  clear eq43472
  have eq43500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq7295 y
       have i₂ := eq43473
       grind)
    | exact superpose eq43473 eq7295
    | (have j0 := eq7295 y
       grind)
    | exact resolve eq7295 eq43473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7295
  have eq43516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq43500
  have eq43522 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq43516
       have r₂ := eq16
       grind)
    | exact resolve eq43516 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43516
  have eq43581 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq43522
  have eq43634 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ x = y := by
    first
    | (have i₁ := eq64 y
       have i₂ := eq43581
       grind)
    | exact superpose eq43581 eq64
    | exact resolve eq64 eq43581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq43703 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq43634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq43634
    | exact resolve eq43634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43634
  have eq43727 : (k y y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq43581 eq43703
    | exact resolve eq43703 eq43581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43581 eq43703
  have eq43745 : y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq43727
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq43727
    | exact resolve eq43727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43727
  have eq43782 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq43745
       grind)
    | exact superpose eq43745 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq43745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43745
  have eq43783 : y = (M.op y y) ∨ x = y := by grind
  clear eq43782
  have eq43802 : x = y ∨ x = y := by
    first
    | exact superpose eq43473 eq43783
    | exact resolve eq43783 eq43473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43473 eq43783
  have eq43803 : x = y := by grind
  clear eq43802
  have eq43832 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43803
       grind)
    | exact superpose eq43803 eq16
    | exact resolve eq16 eq43803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43833 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38897
       have i₂ := eq43803
       grind)
    | exact superpose eq43803 eq38897
    | exact resolve eq38897 eq43803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38897 eq43803
  have eq43869 : x = (M.op x x) := by grind
  clear eq43833
  have eq43917 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4779 x
       have i₂ := eq43869
       grind)
    | exact superpose eq43869 eq4779
    | (have j0 := eq4779 x
       grind)
    | exact resolve eq4779 eq43869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq43926 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43917
  have eq43933 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43926
       have i₂ := eq43869
       grind)
    | exact superpose eq43869 eq43926
    | exact resolve eq43926 eq43869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43926
  have eq43934 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq43933
  have eq43956 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq43832
       have i₂ := eq43869
       grind)
    | exact superpose eq43869 eq43832
    | exact resolve eq43832 eq43869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43832 eq43869
  have eq43957 : False := by grind
  exact eq43957

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation3868 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq472 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3195 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq472 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq472
    | exact resolve eq472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq3245 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3195 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3195
    | (have j0 := eq3195 X0 X1
       grind)
    | exact resolve eq3195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3249 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3245 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3245
    | (have j0 := eq3245 (τ X1) (τ X0)
       grind)
    | exact resolve eq3245 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3343 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3249 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3249
    | (have j0 := eq3249 X0 X1
       grind)
    | exact resolve eq3249 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq18768 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3343 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3343 X0 X1
       grind)
    | exact superpose eq3343 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3343 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3343 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3343 X0 X1
       grind)
    | exact resolve eq13 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq18775 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18768 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18768
  have eq18776 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18775 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18775
  have eq18787 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18776 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq18776
    | (have j0 := eq18776 X0 X1
       grind)
    | exact resolve eq18776 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18776
  have eq25133 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18787 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18787
    | exact resolve eq18787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18787
  have eq25232 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25133 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq25133
    | (have j0 := eq25133 X0 X1
       grind)
    | exact resolve eq25133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133
  have eq25299 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq25232 X1 X0
       grind)
    | exact superpose eq25232 eq10
    | (have j1 := eq25232 X1 X0
       grind)
    | exact resolve eq10 eq25232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25232
  have eq25407 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25299 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq25299
    | (have j0 := eq25299 X0 X1
       grind)
    | exact resolve eq25299 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25299
  have eq25408 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq25407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25407
  have eq25430 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25408 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25408
    | exact resolve eq25408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25477 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq25408 X0 X1
       grind)
    | exact superpose eq25408 eq18
    | (have j1 := eq25408 X0 X1
       grind)
    | exact resolve eq18 eq25408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25408
  have eq25795 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq25430 (σ X0) (σ X1)
       grind)
    | exact superpose eq25430 eq15
    | (have j1 := eq25430 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq25430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25430
  have eq25917 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25477 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25477
    | exact resolve eq25477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25477
  have eq26077 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25917 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25917
    | (have j0 := eq25917 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq25917 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25917
  have eq27595 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25795 x y
       grind)
    | exact superpose eq25795 eq16
    | (have j1 := eq25795 x y
       grind)
    | exact resolve eq16 eq25795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25795
  have eq27679 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27595
       have i₂ := eq26077 x y
       grind)
    | exact superpose eq26077 eq27595
    | (have j1 := eq26077 (σ x) (σ y)
       grind)
    | (have r₁ := eq27595
       have r₂ := eq26077 x y
       grind)
    | (have r₁ := eq27595
       have r₂ := eq26077 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq27595
       have r₂ := eq26077 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq27595 eq26077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26077 eq27595
  have eq27684 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq27679
  have eq27688 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27684
       grind)
    | exact superpose eq27684 eq16
    | exact resolve eq16 eq27684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27684
  have eq27689 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq27688
       have r₂ := eq22 x
       grind)
    | exact resolve eq27688 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27688
  have eq27690 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27689
       grind)
    | exact superpose eq27689 eq16
    | exact resolve eq16 eq27689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27691 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27689
       grind)
    | exact superpose eq27689 eq10
    | exact resolve eq10 eq27689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27689
  have eq27861 : x = y := by
    first
    | (have i₁ := eq27691
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27691
    | exact resolve eq27691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27691
  have eq27862 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27690
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27690
    | exact resolve eq27690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27690
  have eq27863 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27862
       have i₂ := eq27861
       grind)
    | exact superpose eq27861 eq27862
    | exact resolve eq27862 eq27861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27861 eq27862
  have eq27864 : False := by grind
  exact eq27864

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3868 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq4012 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq94 X1 X0
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq94 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq94 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4027 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4012 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012
  have eq4028 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4027 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027
  have eq6090 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4028 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4028
    | exact resolve eq4028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6121 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4028 X0 X1
       grind)
    | exact superpose eq4028 eq37
    | (have j1 := eq4028 X0 X1
       grind)
    | exact resolve eq37 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4028
  have eq6213 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6121 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6121
    | (have j0 := eq6121 X0 X1
       grind)
    | exact resolve eq6121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6220 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6090 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq6090
    | (have j0 := eq6090 X0 X1
       grind)
    | exact resolve eq6090 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6090
  have eq6373 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq6220 X1 X0
       grind)
    | exact superpose eq6220 eq11
    | (have j1 := eq6220 X1 X0
       grind)
    | exact resolve eq11 eq6220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6220
  have eq6494 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6373 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq6373
    | (have j0 := eq6373 X0 X1
       grind)
    | exact resolve eq6373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6373
  have eq6536 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq6494 (τ X0) X1
       grind)
    | exact superpose eq6494 eq19
    | (have j1 := eq6494 (τ X0) X1
       grind)
    | exact resolve eq19 eq6494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq6494
  have eq6816 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6213 (τ X1) X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq6213
    | (have j0 := eq6213 (τ X0) X1
       grind)
    | exact resolve eq6213 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq6213
  have eq6949 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6816 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6816
    | (have j0 := eq6816 X0 X1
       grind)
    | exact resolve eq6816 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq6989 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6949 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6949
    | (have j0 := eq6949 X0 X1
       grind)
    | exact resolve eq6949 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6949
  have eq7124 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq6989 X1 X0
       grind)
    | exact superpose eq6989 eq11
    | (have j1 := eq6989 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq6989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7247 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7124 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq7124
    | (have j0 := eq7124 X0 X1
       grind)
    | exact resolve eq7124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124
  have eq7502 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7247 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7247
    | (have j0 := eq7247 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq7247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7247
  have eq7676 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7502 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7502
    | (have j0 := eq7502 X0 X1
       grind)
    | exact resolve eq7502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7502
  have eq7685 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7676 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7676
    | (have j0 := eq7676 X0 X1
       grind)
    | exact resolve eq7676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676
  have eq8428 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6536 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6536
    | exact resolve eq6536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq8517 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8428 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8428
    | (have j0 := eq8428 X0 X1
       grind)
    | exact resolve eq8428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8428
  have eq9236 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7685 y x
       grind)
    | exact superpose eq7685 eq16
    | (have j1 := eq7685 x y
       grind)
    | exact resolve eq16 eq7685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685
  have eq9299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9236
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq9236
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq9236
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq9236
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq9236 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9300 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq9236
       have i₂ := eq8517 x y
       grind)
    | exact superpose eq8517 eq9236
    | (have j1 := eq8517 x y
       grind)
    | (have r₁ := eq9236
       have r₂ := eq8517 x y
       grind)
    | (have r₁ := eq9236
       have r₂ := eq8517 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq9236
       have r₂ := eq8517 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq9236 eq8517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8517 eq9236
  have eq9303 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq9300
  have eq9304 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq9303
  have eq9305 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq9299
  have eq9306 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9305
  have eq9516 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9304
       grind)
    | exact superpose eq9304 eq16
    | exact resolve eq16 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq9517 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9516
       have r₂ := eq22 x
       grind)
    | exact resolve eq9516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9516
  have eq9522 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq268 x y
       have i₂ := eq9517
       grind)
    | exact superpose eq9517 eq268
    | (have j0 := eq268 x y
       grind)
    | exact resolve eq268 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq9517
  have eq9540 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9522
  have eq9541 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9540
  have eq9765 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9306
       grind)
    | exact superpose eq9306 eq16
    | exact resolve eq16 eq9306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9306
  have eq9766 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9765
       have r₂ := eq22 x
       grind)
    | exact resolve eq9765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9765
  have eq9904 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9541
       grind)
    | exact superpose eq9541 eq16
    | exact resolve eq16 eq9541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541
  have eq9945 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9904
       have i₂ := eq9766
       grind)
    | exact superpose eq9766 eq9904
    | exact resolve eq9904 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766 eq9904
  have eq9949 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq9945
  have eq9950 : (σ x) = (σ y) := by grind
  clear eq9949
  have eq10077 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9950
       grind)
    | exact superpose eq9950 eq16
    | exact resolve eq16 eq9950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10078 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9950
       grind)
    | exact superpose eq9950 eq10
    | exact resolve eq10 eq9950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950
  have eq10170 : x = y := by
    first
    | (have i₁ := eq10078
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10078
    | exact resolve eq10078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078
  have eq10171 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10077
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10077
    | exact resolve eq10077 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10077
  have eq10172 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10171
       have i₂ := eq10170
       grind)
    | exact superpose eq10170 eq10171
    | exact resolve eq10171 eq10170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10170 eq10171
  have eq10173 : False := by grind
  exact eq10173
