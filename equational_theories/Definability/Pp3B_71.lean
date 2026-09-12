import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_x_pyy_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq194
    | (have j0 := eq194 X0 X1
       grind)
    | exact resolve eq194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq199 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq190 X1 X0
       grind)
    | (have r₁ := eq196 X1 X0
       have r₂ := eq190 X0 X1
       grind)
    | (have r₁ := eq196 X1 (k X0 X1)
       have r₂ := eq190 X0 X1
       grind)
    | (have r₁ := eq196 X1 X1
       have r₂ := eq190 X1 X1
       grind)
    | exact resolve eq196 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq196
  have eq680 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq199 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq199
    | exact resolve eq199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 y x
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 y x
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq708 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq680
  have eq714 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq708
    | exact resolve eq708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq823 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq714 (τ X0) X1
       grind)
    | exact superpose eq714 eq18
    | (have j1 := eq714 (τ X0) X1
       grind)
    | exact resolve eq18 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1065 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq823 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq823
    | exact resolve eq823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1117 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1065
    | (have j0 := eq1065 X0 X1
       grind)
    | exact resolve eq1065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1776 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq1117 x y
       grind)
    | exact superpose eq1117 eq687
    | (have j1 := eq1117 (σ x) (σ y)
       grind)
    | (have r₁ := eq687
       have r₂ := eq1117 x y
       grind)
    | exact resolve eq687 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1777 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1776
  have eq1784 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq1790 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35 y y
       have i₂ := eq1777
       grind)
    | exact superpose eq1777 eq35
    | exact resolve eq35 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1868 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq687
       have i₂ := eq1784
       grind)
    | exact superpose eq1784 eq687
    | exact resolve eq687 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq1784
  have eq1873 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1868
  have eq2004 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1873
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq1873
    | exact resolve eq1873 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790 eq1873
  have eq2005 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2004
  have eq2006 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2005
  have eq2013 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq2006
       grind)
    | exact superpose eq2006 eq43
    | exact resolve eq43 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2027 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 (σ y) (σ y)
       have i₂ := eq2006
       grind)
    | exact superpose eq2006 eq35
    | exact resolve eq35 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2046 : x = (k x y) := by
    first
    | (have i₁ := eq2013
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2013
    | exact resolve eq2013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2102 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq714 x y
       have i₂ := eq2046
       grind)
    | exact superpose eq2046 eq714
    | (have j0 := eq714 x y
       grind)
    | exact resolve eq714 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq2046
  have eq2282 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq16
    | exact resolve eq16 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2451 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2282
       have i₂ := eq2102
       grind)
    | exact superpose eq2102 eq2282
    | exact resolve eq2282 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2476 : x = (M.op y y) := by grind
  clear eq2451
  have eq2613 : x = (M.op x y) := by
    first
    | (have i₁ := eq35 y y
       have i₂ := eq2476
       grind)
    | exact superpose eq2476 eq35
    | exact resolve eq35 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2476
  have eq2633 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2282
       have i₂ := eq2613
       grind)
    | exact superpose eq2613 eq2282
    | exact resolve eq2282 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282 eq2613
  have eq2659 : False := by grind
  exact eq2659

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation442 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law442 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq252 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (τ X0) X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq569 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq548
  have eq7657 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq569 X0 X1
       grind)
    | exact superpose eq569 eq10
    | (have j1 := eq569 X0 X1
       grind)
    | exact resolve eq10 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq7731 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (M.op X1 X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7657 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq7657
    | (have j0 := eq7657 X0 X1
       grind)
    | exact resolve eq7657 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7657
  have eq250666 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7731 X1 X0
       have j1 := eq252 X0 X1
       grind)
    | (have r₁ := eq7731 X1 X0
       have r₂ := eq252 X0 X1
       grind)
    | (have r₁ := eq7731 (M.op X1 (τ X0)) (M.op X0 X0)
       have r₂ := eq252 X0 X1
       grind)
    | exact resolve eq7731 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq251676 : ∀ X0 X1 : G, (τ (M.op X1 X1)) ≠ (M.op X0 (τ X1)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250666 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250666
  have eq251686 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq251676 X0 X1
       have j1 := eq7731 X0 X1
       grind)
    | (have r₁ := eq251676 X0 X1
       have r₂ := eq7731 X0 X1
       grind)
    | (have r₁ := eq251676 X0 X1
       have r₂ := eq7731 (M.op X0 (τ X1)) (M.op X1 X1)
       grind)
    | exact resolve eq251676 eq7731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7731 eq251676
  have eq252121 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq251686 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq251686
    | exact resolve eq251686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251686
  have eq252489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq252121 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq252121
    | (have j0 := eq252121 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq252121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255022 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252489 X0 X1
       have i₂ := eq252121 X1 X0
       grind)
    | exact superpose eq252121 eq252489
    | (have j0 := eq252489 X0 X1
       have j1 := eq252121 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq252489 eq252121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252121 eq252489
  have eq256564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq255022 x y
       grind)
    | exact superpose eq255022 eq16
    | (have j1 := eq255022 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq255022 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq255022 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq255022 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq255022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255022
  have eq256766 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq256564
  have eq256844 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq256766
       grind)
    | exact superpose eq256766 eq10
    | exact resolve eq10 eq256766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256766
  have eq257078 : x = y ∨ x = y := by
    first
    | (have i₁ := eq256844
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq256844
    | exact resolve eq256844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256844
  have eq257079 : x = y := by grind
  clear eq257078
  have eq257082 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq257079
       grind)
    | exact superpose eq257079 eq16
    | exact resolve eq16 eq257079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257079
  have eq257083 : False := by grind
  exact eq257083

/-- `Equation4425`: `x ◇ (x ◇ y) = (z ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4425 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4425 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4425.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X2) := by
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
  clear eq35
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq385 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq301
    | exact resolve eq301 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq551 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X4 x X0 X1
       grind)
    | (have i₁ := eq177 X2 X3 X4 (M.op X4 x)
       have i₂ := eq177 X0 X1 X4 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X4) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4
       have i₂ := eq177 X0 X1 X2 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq570 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq551 x x X2 X3 X4
       have i₂ := eq557 x x
       grind)
    | (have i₁ := eq551 (σ x) (σ y) X2 X3 X4
       have i₂ := eq557 x x
       grind)
    | exact superpose eq557 eq551
    | (have j0 := eq551 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq551 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq580 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq570 x x X4
       have i₂ := eq557 x x
       grind)
    | (have i₁ := eq570 (σ x) (σ y) X4
       have i₂ := eq557 x x
       grind)
    | exact superpose eq557 eq570
    | (have j0 := eq570 (σ x) (σ y) X4
       grind)
    | exact resolve eq570 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq603 : ∀ X2 : G, (M.op (M.op X2 X2) X2) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | (have i₁ := eq16 x x X2
       have i₂ := eq557 x x
       grind)
    | (have i₁ := eq16 (σ x) (σ y) X2
       have i₂ := eq557 x x
       grind)
    | exact superpose eq557 eq16
    | (have j0 := eq16 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq580 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq580 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq657 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq580 (M.op sF2 sF4)
       have i₂ := eq631 (M.op sF2 sF4)
       grind)
    | exact superpose eq631 eq580
    | exact resolve eq580 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq631 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq631
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq844 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq860 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq2322 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq842
       grind)
    | exact superpose eq842 eq40
    | exact resolve eq40 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2323 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2322
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2322
    | exact resolve eq2322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2325 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2323
    | exact resolve eq2323 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq16862 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq631 (M.op sF2 sF4)
       have i₂ := eq860 (M.op sF2 sF4)
       grind)
    | exact superpose eq860 eq631
    | (have j1 := eq860 X0
       grind)
    | exact resolve eq631 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq16978 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16862 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16862 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq16862 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16862
  have eq17092 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq603 X0
       have i₂ := eq16978 X0
       grind)
    | exact superpose eq16978 eq603
    | exact resolve eq603 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17093 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq631 X0
       have i₂ := eq16978 X0
       grind)
    | exact superpose eq16978 eq631
    | exact resolve eq631 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17107 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq557 X0 X0
       have i₂ := eq16978 X0
       grind)
    | exact superpose eq16978 eq557
    | exact resolve eq557 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17169 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17092 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq17092
    | exact resolve eq17092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq17251 : ∀ X0 : G, (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y)))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq17093 (σ X0)
       grind)
    | exact superpose eq17093 eq10
    | exact resolve eq10 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17093
  have eq17550 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17107 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq17107
    | exact resolve eq17107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17551 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq17107 (τ X0)
       have i₂ := eq385 X0 X0
       grind)
    | exact superpose eq385 eq17107
    | exact resolve eq17107 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20499 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq657 eq17169
    | exact resolve eq17169 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20670 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq20499
       have i₂ := eq631 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq631 eq20499
    | exact resolve eq20499 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq20499
  have eq21202 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq657 eq17251
    | exact resolve eq17251 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq17251
  have eq21479 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20670 eq21202
    | exact resolve eq21202 eq20670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20670 eq21202
  have eq31392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2325 eq844
    | exact resolve eq844 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq2325
  have eq31399 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq31392
       have r₂ := eq27
       grind)
    | exact resolve eq31392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31405 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31399
       have i₂ := eq16978 sF2
       grind)
    | exact superpose eq16978 eq31399
    | exact resolve eq31399 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31399
  have eq31409 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31405
       have i₂ := eq16978 sF3
       grind)
    | exact superpose eq16978 eq31405
    | exact resolve eq31405 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31405
  have eq31413 : y = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31409
       have i₂ := eq16978 x
       grind)
    | exact superpose eq16978 eq31409
    | exact resolve eq31409 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31409
  have eq31415 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31413
       have i₂ := eq16978 y
       grind)
    | exact superpose eq16978 eq31413
    | exact resolve eq31413 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31413
  have eq31422 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31415 eq152
    | exact resolve eq152 eq31415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq31415
  have eq31464 : y = (k y y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq31422
    | exact resolve eq31422 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31422
  have eq31465 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (k y y) := by grind
  clear eq31464
  have eq31492 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31465 eq97
    | exact resolve eq97 eq31465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq31465
  have eq31527 : y = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq31492
    | exact resolve eq31492 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31492
  have eq31528 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq31527
  have eq31545 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq31528
       grind)
    | exact superpose eq31528 eq40
    | exact resolve eq40 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31556 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq17107 y
       have i₂ := eq31528
       grind)
    | exact superpose eq31528 eq17107
    | exact resolve eq17107 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31559 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq17550 y
       have i₂ := eq31528
       grind)
    | exact superpose eq31528 eq17550
    | exact resolve eq17550 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31560 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq17551 y
       have i₂ := eq31528
       grind)
    | exact superpose eq31528 eq17551
    | exact resolve eq17551 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq31573 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31560
       have i₂ := eq16978 (τ y)
       grind)
    | exact superpose eq16978 eq31560
    | exact resolve eq31560 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31560
  have eq31574 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31559
       have i₂ := eq16978 (σ y)
       grind)
    | exact superpose eq16978 eq31559
    | exact resolve eq31559 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31559
  have eq31577 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31556
       have i₂ := eq16978 y
       grind)
    | exact superpose eq16978 eq31556
    | exact resolve eq31556 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31556
  have eq31587 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31545
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31545
    | exact resolve eq31545 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31545
  have eq31595 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31573
       have i₂ := eq385 y y
       grind)
    | exact superpose eq385 eq31573
    | exact resolve eq31573 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq31573
  have eq31596 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31574
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq31574
    | exact resolve eq31574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31574
  have eq31599 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31528 eq31577
    | exact resolve eq31577 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31577
  have eq31611 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq31528 eq31595
    | exact resolve eq31595 eq31528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31528 eq31595
  have eq31612 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31596
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq31596
    | exact resolve eq31596 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq31596
  have eq31620 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq31599 eq31611
    | exact resolve eq31611 eq31599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31611
  have eq31621 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq31612
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31612
    | exact resolve eq31612 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31612
  have eq31629 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq31587 eq31621
    | exact resolve eq31621 eq31587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31587 eq31621
  have eq32323 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq17107 x
       have i₂ := eq31620
       grind)
    | exact superpose eq31620 eq17107
    | exact resolve eq17107 eq31620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32326 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq17550 x
       have i₂ := eq31620
       grind)
    | exact superpose eq31620 eq17550
    | exact resolve eq17550 eq31620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31620
  have eq32334 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32326
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32326
    | exact resolve eq32326 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32326
  have eq32336 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32323
    | exact resolve eq32323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32323
  have eq32350 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq32334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32334
    | exact resolve eq32334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32334
  have eq32360 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq32350
    | exact resolve eq32350 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32350
  have eq32365 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32336 eq32360
    | exact resolve eq32360 eq32336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32360
  have eq32374 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq32365
       grind)
    | exact superpose eq32365 eq14
    | exact resolve eq14 eq32365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32365
  have eq32431 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32374
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32374
    | exact resolve eq32374 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32374
  have eq32456 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32431 eq27
    | exact resolve eq27 eq32431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32431
  have eq32927 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq32336 eq21479
    | exact resolve eq21479 eq32336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32336
  have eq32950 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq32927
    | exact resolve eq32927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32927
  have eq33045 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq32950
       grind)
    | exact superpose eq32950 eq14
    | exact resolve eq14 eq32950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32950
  have eq33102 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq33045
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33045
    | exact resolve eq33045 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33045
  have eq33110 : y = (σ y) := by
    first
    | (have r₁ := eq33102
       have r₂ := eq32456
       grind)
    | exact resolve eq33102 eq32456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32456 eq33102
  have eq33127 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq33110
       grind)
    | exact superpose eq33110 eq18
    | exact resolve eq18 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33128 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq33110
       grind)
    | exact superpose eq33110 eq24
    | exact resolve eq24 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37148 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17107 x
       have i₂ := eq31599
       grind)
    | exact superpose eq31599 eq17107
    | exact resolve eq17107 eq31599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17107
  have eq37151 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17550 x
       have i₂ := eq31599
       grind)
    | exact superpose eq31599 eq17550
    | exact resolve eq17550 eq31599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17550 eq31599
  have eq37162 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37151
    | exact resolve eq37151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37151
  have eq37165 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37148
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37148
    | exact resolve eq37148 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37148
  have eq37187 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37162
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37162
    | exact resolve eq37162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37162
  have eq37190 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37165
       have i₂ := eq33110
       grind)
    | exact superpose eq33110 eq37165
    | exact resolve eq37165 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37165
  have eq37212 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq37187
    | exact resolve eq37187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37187
  have eq37233 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37212
       have i₂ := eq33110
       grind)
    | exact superpose eq33110 eq37212
    | exact resolve eq37212 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37212
  have eq37247 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37190 eq37233
    | exact resolve eq37233 eq37190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37190 eq37233
  have eq37268 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37247 eq580
    | exact resolve eq580 eq37247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37341 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37247 eq557
    | exact resolve eq557 eq37247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37247
  have eq37344 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq37341
    | exact resolve eq37341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37341
  have eq37523 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq37344
  have eq37804 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37268 eq33127
    | exact resolve eq33127 eq37268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37268
  have eq37809 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq37804
       have r₂ := eq37523
       grind)
    | exact resolve eq37804 eq37523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37523 eq37804
  have eq37837 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq37809 eq27
    | exact resolve eq27 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37839 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37809 eq580
    | exact resolve eq580 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq37895 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq37809 eq21479
    | exact resolve eq21479 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479
  have eq38390 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq37839 eq16
    | exact resolve eq16 eq37839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37839
  have eq39080 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq38390 X0 X0
       have i₂ := eq16978 X0
       grind)
    | exact superpose eq16978 eq38390
    | exact resolve eq38390 eq16978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16978
  have eq39658 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq31629 eq557
    | exact resolve eq557 eq31629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq31629
  have eq39663 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq26 eq39658
    | exact resolve eq39658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq39658
  have eq39730 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq37809 eq39663
    | exact resolve eq39663 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39663
  have eq39772 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39730
       have i₂ := eq33110
       grind)
    | exact superpose eq33110 eq39730
    | exact resolve eq39730 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33110 eq39730
  have eq39848 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (σ y)) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq17169 x
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq17169
    | exact resolve eq17169 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17169
  have eq39857 : (M.op (σ x) (M.op x y)) = (M.op x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39080 x
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq39080
    | exact resolve eq39080 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39080 eq39772
  have eq39858 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq33127 eq39857
    | exact resolve eq39857 eq33127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33127 eq39857
  have eq39866 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (σ y)) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39848
    | exact resolve eq39848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39848
  have eq39888 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq33128 eq39866
    | exact resolve eq39866 eq33128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39866
  have eq39905 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq37809 eq39888
    | exact resolve eq39888 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39888
  have eq39917 : (M.op x y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39858 eq39905
    | exact resolve eq39905 eq39858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39905
  have eq40059 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (σ y) (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq39917 eq564
    | exact resolve eq564 eq39917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq40060 : (M.op (σ x) (M.op x y)) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39917 eq38390
    | exact resolve eq38390 eq39917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390 eq39917
  have eq40061 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq39858 eq40060
    | exact resolve eq40060 eq39858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40060
  have eq40062 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq40059 x X1
       have i₂ := eq603 x
       grind)
    | exact superpose eq603 eq40059
    | exact resolve eq40059 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq40059
  have eq40069 : ∀ X1 : G, (M.op (σ x) (M.op x y)) = (M.op X1 (M.op (σ y) (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq37809 eq40062
    | exact resolve eq40062 eq37809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37809 eq40062
  have eq40076 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op (σ y) (M.op x y))) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq39858 eq40069
    | exact resolve eq40069 eq39858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39858 eq40069
  have eq40082 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq40061 eq40076
    | exact resolve eq40076 eq40061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40061 eq40076
  have eq40177 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40082 eq37895
    | exact resolve eq37895 eq40082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37895 eq40082
  have eq40179 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq40177
    | exact resolve eq40177 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40177
  have eq40215 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq40179
       have r₂ := eq37837
       grind)
    | exact resolve eq40179 eq37837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40179
  have eq41755 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40215 eq33128
    | exact resolve eq33128 eq40215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33128 eq40215
  have eq42014 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41755 eq20
    | exact resolve eq20 eq41755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41755
  have eq42178 : False := by grind
  exact eq42178

/-- `Equation4426`: `x ◇ (x ◇ y) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pyx_Equation4426 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq692 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op (M.op x x) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq692 X2 X3 (M.op x x) X5
       have i₂ := eq16 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq16 eq692
    | exact resolve eq692 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq695 X2 X3 X4 (M.op X4 x)
       have i₂ := eq695 X4 x X0 X1
       grind)
    | (have i₁ := eq695 X2 X3 X4 (M.op X4 x)
       have i₂ := eq695 X0 X1 X4 x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | (have j0 := eq695 X0 X1 x y
       grind)
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq695
    | (have j0 := eq695 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq695 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq695 X0 X1 X2 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq749 x x
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq749 (σ x) (σ y)
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq749
    | (have j0 := eq749 (σ x) (σ y)
       have j1 := eq750 x y
       grind)
    | exact resolve eq749 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq771 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq744 x x X2 X3 X4
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq744 (σ x) (σ y) X2 X3 X4
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq744
    | (have j0 := eq744 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq744 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq777 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq771 x x X4
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq771 (σ x) (σ y) X4
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq771
    | (have j0 := eq771 (σ x) (σ y) X4
       grind)
    | exact resolve eq771 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq809 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq692 x (M.op (M.op x x) x) X2 X3
       have i₂ := eq750 (M.op x x) x
       grind)
    | exact superpose eq750 eq692
    | exact resolve eq692 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq832 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq777 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 x (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq777 x
       grind)
    | exact resolve eq28 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq863 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = X0 ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq777 x
       have i₂ := eq11 (M.op sF2 sF4) x
       grind)
    | exact superpose eq11 eq777
    | (have j1 := eq11 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq880 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq885 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq885 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq912 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq868 X0
       have j1 := eq28 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq868 x
       have r₂ := eq28 (M.op (σ x) (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq868 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq28 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq868 (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))))
       have r₂ := eq28 X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq868 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq934 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have j0 := eq912 X0
       have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq912 x
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq912 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq912 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq936 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq886 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq886
    | (have j0 := eq886 (σ X0)
       grind)
    | exact resolve eq886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq836 eq35
    | exact resolve eq35 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq955 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq941 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq941
    | exact resolve eq941 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq999 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq955 eq886
    | (have j0 := eq886 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq886 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq955 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq886 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1012 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq999
  have eq2207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq874
       grind)
    | exact superpose eq874 eq40
    | exact resolve eq40 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2208 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2207
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2207
    | exact resolve eq2207 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2210 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2208
    | exact resolve eq2208 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq22019 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1012 eq809
    | exact resolve eq809 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22026 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1012 eq695
    | exact resolve eq695 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22033 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1012 eq764
    | exact resolve eq764 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22037 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1012 eq22033
    | exact resolve eq22033 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22033
  have eq22041 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1012 eq22026
    | exact resolve eq22026 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22026
  have eq22059 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X2
    first
    | (have i₁ := eq22037 x x X2
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq22037
    | exact resolve eq22037 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22037
  have eq22061 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq22041 x x
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq22041 (σ x) (σ y)
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq22041
    | (have j0 := eq22041 (σ x) (σ y)
       grind)
    | exact resolve eq22041 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041
  have eq22109 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq22061 eq15
    | exact resolve eq15 eq22061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2210 eq880
    | exact resolve eq880 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24992 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24984
       have r₂ := eq27
       grind)
    | exact resolve eq24984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24984
  have eq24999 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24992 eq220
    | exact resolve eq220 eq24992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq24992
  have eq25053 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq24999
    | exact resolve eq24999 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24999
  have eq25062 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq25053
       have r₂ := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq25053
       have r₂ := eq28 y x
       grind)
    | exact resolve eq25053 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25053
  have eq25063 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq25062
       have r₂ := eq13 y x
       grind)
    | exact resolve eq25062 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25062
  have eq25066 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq25063 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq25063
       grind)
    | exact resolve eq28 eq25063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25063
  have eq25076 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq25066
  have eq25105 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) := by
    first
    | exact superpose eq25076 eq142
    | exact resolve eq142 eq25076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq25076
  have eq25108 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq32 eq25105
    | exact resolve eq25105 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25105
  have eq25109 : y = (k y x) := by grind
  clear eq25108
  have eq25120 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq874
       have i₂ := eq25109
       grind)
    | exact superpose eq25109 eq874
    | exact resolve eq874 eq25109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq25122 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq25109
       grind)
    | exact superpose eq25109 eq40
    | exact resolve eq40 eq25109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq25109
  have eq25125 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq25122
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25122
    | exact resolve eq25122 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25122
  have eq25135 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25125 eq880
    | exact resolve eq880 eq25125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq25136 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25125 eq2210
    | exact resolve eq2210 eq25125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq25125
  have eq25769 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq809 y X0
       have i₂ := eq25120
       grind)
    | exact superpose eq25120 eq809
    | exact resolve eq809 eq25120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25779 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq750 y y
       have i₂ := eq25120
       grind)
    | exact superpose eq25120 eq750
    | exact resolve eq750 eq25120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25120
  have eq25837 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25135 eq809
    | exact resolve eq809 eq25135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25847 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25135 eq750
    | exact resolve eq750 eq25135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25135
  have eq25900 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq809 y X0
       have i₂ := eq25136
       grind)
    | exact superpose eq25136 eq809
    | exact resolve eq809 eq25136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25136
  have eq26049 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25769 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq25769 x
       grind)
    | exact superpose eq25769 eq18
    | (have j1 := eq25769 y
       grind)
    | exact resolve eq18 eq25769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25769
  have eq26151 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26049 eq836
    | exact resolve eq836 eq26049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26232 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26049 eq22061
    | exact resolve eq22061 eq26049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26049
  have eq26258 : x = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26232
    | exact resolve eq26232 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26232
  have eq26591 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq750 y x
       have i₂ := eq26258
       grind)
    | exact superpose eq26258 eq750
    | exact resolve eq750 eq26258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26598 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26258 eq26591
    | exact resolve eq26591 eq26258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26258 eq26591
  have eq26729 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26598 eq22019
    | exact resolve eq22019 eq26598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26732 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26598 eq22061
    | exact resolve eq22061 eq26598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26598
  have eq26761 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26732
    | exact resolve eq26732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26732
  have eq26764 : ∀ X0 : G, x = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26729 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26729
    | (have j0 := eq26729 X0
       grind)
    | exact resolve eq26729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26729
  have eq26846 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26761 eq26764
    | exact resolve eq26764 eq26761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26761 eq26764
  have eq29040 : (σ x) = (σ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26846 eq22061
    | exact resolve eq22061 eq26846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26846
  have eq30423 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y x) X2) ∨ (k X3 (M.op x y)) = X3 ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 y x X0 X1 X2
       have i₂ := eq26151 X3
       grind)
    | exact superpose eq26151 eq710
    | (have j1 := eq26151 X3
       grind)
    | exact resolve eq710 eq26151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30424 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq750 y x
       have i₂ := eq26151 X0
       grind)
    | exact superpose eq26151 eq750
    | (have j1 := eq26151 X0
       grind)
    | exact resolve eq750 eq26151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30431 : ∀ X0 : G, x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26151 eq30424
    | (have j0 := eq30424 X0
       have j1 := eq26151 X0
       grind)
    | exact resolve eq30424 eq26151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30424
  have eq30432 : ∀ X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op y x) X2) ∨ (k X3 (M.op x y)) = X3 ∨ y = (M.op x y) := by
    intro X2 X3
    first
    | (have i₁ := eq30423 x x X2 X3
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq30423
    | (have j0 := eq30423 x x X2 X3
       grind)
    | exact resolve eq30423 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30423
  have eq30441 : ∀ X2 X3 : G, x = (M.op (M.op y x) X2) ∨ (k X3 (M.op x y)) = X3 ∨ y = (M.op x y) := by
    intro X2 X3
    first
    | exact superpose eq30431 eq30432
    | (have j0 := eq30432 X2 X3
       have j1 := eq30431 X3
       grind)
    | exact resolve eq30432 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30432
  have eq30448 : ∀ X2 X3 : G, x = (M.op x X2) ∨ (k X3 (M.op x y)) = X3 ∨ y = (M.op x y) := by
    intro X2 X3
    first
    | exact superpose eq26151 eq30441
    | (have j0 := eq30441 X2 X3
       have j1 := eq26151 X3
       grind)
    | exact resolve eq30441 eq26151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26151 eq30441
  have eq30833 : ∀ X0 X1 : G, (k X1 (M.op x y)) = X1 ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0
       have i₂ := eq30431 (M.op sF2 sF4)
       grind)
    | exact superpose eq30431 eq836
    | (have j1 := eq30431 X1
       grind)
    | exact resolve eq836 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30835 : ∀ X0 X1 : G, x = (k x X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0
       have i₂ := eq30431 (M.op sF2 sF4)
       grind)
    | exact superpose eq30431 eq934
    | (have j1 := eq30431 X1
       grind)
    | exact resolve eq934 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq30912 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22019 X0
       have i₂ := eq30431 (M.op sF2 sF4)
       grind)
    | exact superpose eq30431 eq22019
    | (have j1 := eq30431 X1
       grind)
    | exact resolve eq22019 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30915 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22061
       have i₂ := eq30431 (M.op sF2 sF4)
       grind)
    | exact superpose eq30431 eq22061
    | (have j1 := eq30431 X0
       grind)
    | exact resolve eq22061 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30948 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30915 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30915
    | (have j0 := eq30915 X0
       grind)
    | exact resolve eq30915 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30915
  have eq30951 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq30912 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30912
    | (have j0 := eq30912 X0 X1
       grind)
    | exact resolve eq30912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30912
  have eq31034 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq30948 eq30951
    | (have j0 := eq30951 X0 X1
       have j1 := eq30948 X1
       grind)
    | exact resolve eq30951 eq30948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30951
  have eq33179 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq30448 y X0
       grind)
    | exact superpose eq30448 eq18
    | (have j1 := eq30448 y X0
       grind)
    | exact resolve eq18 eq30448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30448
  have eq33325 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33179 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq33179 (M.op x y)
       grind)
    | exact resolve eq886 eq33179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33179
  have eq33381 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq33325
  have eq33550 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33381 eq750
    | exact resolve eq750 eq33381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33557 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33381 eq33550
    | exact resolve eq33550 eq33381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33550
  have eq35072 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq886 X0
       have i₂ := eq30833 (k X0 X0) x
       grind)
    | exact superpose eq30833 eq886
    | (have j0 := eq886 (M.op x y)
       have j1 := eq30833 X0 x
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq30833 X0 (M.op x y)
       grind)
    | (have r₁ := eq886 x
       have r₂ := eq30833 x x
       grind)
    | exact resolve eq886 eq30833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30833
  have eq35128 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq35072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35072
  have eq35181 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33381 eq35128
    | exact resolve eq35128 eq33381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33381 eq35128
  have eq35318 : x ≠ x ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq30835 (M.op x y) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30835
  have eq35319 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq35318
  have eq35385 : x ≠ x ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35319 eq863
    | (have j0 := eq863 x (M.op x y)
       grind)
    | (have r₁ := eq863 x (M.op x y)
       have r₂ := eq35319
       grind)
    | exact resolve eq863 eq35319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq35319
  have eq35386 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq35385
  have eq35387 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq769 eq35386
    | exact resolve eq35386 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35386
  have eq35392 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33557 eq35387
    | exact resolve eq35387 eq33557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35387
  have eq35394 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33557 eq35392
    | exact resolve eq35392 eq33557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33557 eq35392
  have eq35395 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq35394
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq35394 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35394
  have eq36981 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq31034 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq31034 eq26
    | (have j1 := eq31034 (σ y) X0
       grind)
    | exact resolve eq26 eq31034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31034
  have eq37366 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36981 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq36981 (M.op x y)
       grind)
    | exact resolve eq886 eq36981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36981
  have eq37424 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37366
  have eq40702 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq750 X0 x
       have i₂ := eq35181 (M.op X0 x)
       grind)
    | exact superpose eq35181 eq750
    | (have j1 := eq35181 X0
       grind)
    | exact resolve eq750 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40709 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30431 eq40702
    | (have j0 := eq40702 X0
       have j1 := eq30431 X0
       grind)
    | exact resolve eq40702 eq30431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30431 eq40702
  have eq40732 : ∀ X0 : G, (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30948 eq40709
    | (have j0 := eq40709 X0
       have j1 := eq30948 X0
       grind)
    | exact resolve eq40709 eq30948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948 eq40709
  have eq40749 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35181 eq40732
    | (have j0 := eq40732 X0
       have j1 := eq35181 X0
       grind)
    | exact resolve eq40732 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35181 eq40732
  have eq40772 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40749 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq40749 (M.op x y)
       grind)
    | exact resolve eq886 eq40749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40776 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40749 eq936
    | (have j0 := eq936 (M.op x y)
       grind)
    | exact resolve eq936 eq40749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq40749
  have eq40829 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq40776
  have eq40830 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq40772
  have eq40877 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq40829
    | exact resolve eq40829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40829
  have eq40951 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40830 eq750
    | exact resolve eq750 eq40830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40958 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40830 eq40951
    | exact resolve eq40951 eq40830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40951
  have eq41382 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40877 eq750
    | exact resolve eq750 eq40877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41392 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40877 eq41382
    | exact resolve eq41382 eq40877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40877 eq41382
  have eq41417 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40958 eq41392
    | exact resolve eq41392 eq40958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40958 eq41392
  have eq41628 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41417 eq29040
    | exact resolve eq29040 eq41417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29040 eq41417
  have eq41673 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq41628
  have eq41703 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq41673
    | exact resolve eq41673 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41673
  have eq41704 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq41703
  have eq47780 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35395 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq35395
       grind)
    | exact resolve eq886 eq35395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35395
  have eq47792 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq47780
  have eq47804 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37424 eq47792
    | exact resolve eq47792 eq37424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37424 eq47792
  have eq47818 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40830 eq47804
    | exact resolve eq47804 eq40830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40830 eq47804
  have eq47819 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq47818
  have eq47887 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47819 eq750
    | exact resolve eq750 eq47819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47900 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47819 eq47887
    | exact resolve eq47887 eq47819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47819 eq47887
  have eq59757 : (k x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25779
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq25779
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq25779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25779
  have eq59795 : (k x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq59757
       have r₂ := eq176
       grind)
    | exact resolve eq59757 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59757
  have eq59800 : (k x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq28 x y
       grind)
    | (have r₁ := eq59795
       have r₂ := eq28 x y
       grind)
    | exact resolve eq59795 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59795
  have eq59801 : (k x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq59800
       have r₂ := eq13 x y
       grind)
    | exact resolve eq59800 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59800
  have eq59911 : (k x y) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | exact superpose eq59801 eq22061
    | exact resolve eq22061 eq59801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59929 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq59801 eq47900
    | exact resolve eq47900 eq59801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59801
  have eq59957 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq59929
       have r₂ := eq176
       grind)
    | exact resolve eq59929 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq59929
  have eq59970 : (k x y) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq59911
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq59911
    | exact resolve eq59911 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59911
  have eq60070 : (k x y) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq59970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59970
    | exact resolve eq59970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59970
  have eq60154 : (M.op x y) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq59957 eq60070
    | exact resolve eq60070 eq59957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60070
  have eq61386 : x ≠ (M.op x y) ∨ x = (k x y) := by grind
  clear eq59957
  have eq64937 : ∀ X0 X1 : G, (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq25837 eq836
    | exact resolve eq836 eq25837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25837
  have eq65377 : (k (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25847
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq25847
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq25847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25847
  have eq65408 : (k (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq65377
       have r₂ := eq177
       grind)
    | exact resolve eq65377 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65377
  have eq65412 : (k (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | (have r₁ := eq65408
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq65408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65408
  have eq65413 : (k (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq65412
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq65412 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65412
  have eq65526 : (k (σ x) (σ y)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq65413 eq22109
    | exact resolve eq22109 eq65413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65544 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq65413 eq47900
    | exact resolve eq47900 eq65413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65585 : (k x y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq99 eq65526
    | exact resolve eq65526 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq65526
  have eq68676 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25900 y
       grind)
    | exact superpose eq25900 eq18
    | (have j1 := eq25900 y
       grind)
    | exact resolve eq18 eq25900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25900
  have eq68791 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47900 eq68676
    | exact resolve eq68676 eq47900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47900 eq68676
  have eq68831 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq68791 eq836
    | exact resolve eq836 eq68791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq68791
  have eq79279 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) x) X2) ∨ (k X3 (M.op x y)) = X3 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X0 X1 X2 X3 x
       have i₂ := eq68831 (M.op X0 X1)
       grind)
    | exact superpose eq68831 eq710
    | (have j1 := eq68831 X3
       grind)
    | exact resolve eq710 eq68831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79280 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq750 X0 x
       have i₂ := eq68831 (M.op X0 x)
       grind)
    | exact superpose eq68831 eq750
    | (have j1 := eq68831 X0
       grind)
    | exact resolve eq750 eq68831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79290 : ∀ X0 : G, x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq68831 eq79280
    | (have j0 := eq79280 X0
       have j1 := eq68831 X0
       grind)
    | exact resolve eq79280 eq68831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79280
  have eq79291 : ∀ X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) X2) ∨ (k X3 (M.op x y)) = X3 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2 X3
    first
    | (have i₁ := eq79279 x x X2 X3
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq79279
    | (have j0 := eq79279 x x X2 X3
       grind)
    | exact resolve eq79279 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79279
  have eq79299 : ∀ X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X2) ∨ (k X3 (M.op x y)) = X3 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2 X3
    first
    | exact superpose eq68831 eq79291
    | (have j0 := eq79291 X2 X3
       have j1 := eq68831 X3
       grind)
    | exact resolve eq79291 eq68831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68831 eq79291
  have eq79304 : ∀ X2 X3 : G, x = (M.op x X2) ∨ (k X3 (M.op x y)) = X3 ∨ (σ (M.op x y)) = (σ y) := by
    intro X2 X3
    first
    | exact superpose eq79290 eq79299
    | (have j0 := eq79299 X2 X3
       have j1 := eq79290 X3
       grind)
    | exact resolve eq79299 eq79290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79299
  have eq79912 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq22019 X0
       have i₂ := eq79290 (M.op sF2 sF4)
       grind)
    | exact superpose eq79290 eq22019
    | (have j1 := eq79290 X1
       grind)
    | exact resolve eq22019 eq79290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22019
  have eq79915 : ∀ X0 : G, x = (σ x) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq22061
       have i₂ := eq79290 (M.op sF2 sF4)
       grind)
    | exact superpose eq79290 eq22061
    | (have j1 := eq79290 X0
       grind)
    | exact resolve eq22061 eq79290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79290
  have eq79977 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq79915 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79915
    | (have j0 := eq79915 X0
       grind)
    | exact resolve eq79915 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79915
  have eq79980 : ∀ X0 X1 : G, x = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq79912 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79912
    | (have j0 := eq79912 X0 X1
       grind)
    | exact resolve eq79912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79912
  have eq80064 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq79977 eq79980
    | (have j0 := eq79980 X0 X1
       have j1 := eq79977 X1
       grind)
    | exact resolve eq79980 eq79977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79980
  have eq80146 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq79977 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq79977 (M.op x y)
       grind)
    | exact resolve eq886 eq79977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79977
  have eq80221 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq80146
  have eq80434 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80221 eq750
    | exact resolve eq750 eq80221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80446 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq80221 eq80434
    | exact resolve eq80434 eq80221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80221 eq80434
  have eq82243 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq79304 y X0
       grind)
    | exact superpose eq79304 eq18
    | (have j1 := eq79304 y X0
       grind)
    | exact resolve eq18 eq79304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79304
  have eq82428 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82243 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq82243 (M.op x y)
       grind)
    | exact resolve eq886 eq82243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82243
  have eq82503 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq82428
  have eq83347 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq82503 eq809
    | exact resolve eq809 eq82503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83364 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82503 eq750
    | exact resolve eq750 eq82503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83376 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82503 eq83364
    | exact resolve eq83364 eq82503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82503 eq83364
  have eq87680 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq80064 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq80064 eq26
    | (have j1 := eq80064 (σ y) X0
       grind)
    | exact resolve eq26 eq80064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80064
  have eq88144 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq87680 eq886
    | (have j0 := eq886 (M.op x y)
       grind)
    | (have r₁ := eq886 (M.op x y)
       have r₂ := eq87680 (M.op x y)
       grind)
    | exact resolve eq886 eq87680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87680
  have eq88218 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq88144
  have eq88444 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88218 eq750
    | exact resolve eq750 eq88218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88454 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq88218 eq88444
    | exact resolve eq88444 eq88218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88218 eq88444
  have eq88518 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq88454 eq777
    | exact resolve eq777 eq88454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107128 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq64937
    | (have j0 := eq64937 (σ y) X0
       grind)
    | exact resolve eq64937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64937
  have eq107425 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ y) (σ x)) X2) ∨ (k X3 (M.op (σ x) (σ y))) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X0 X1 X2 X3 x
       have i₂ := eq107128 (M.op X0 X1)
       grind)
    | exact superpose eq107128 eq710
    | (have j1 := eq107128 X3
       grind)
    | exact resolve eq710 eq107128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq107426 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq750 X0 x
       have i₂ := eq107128 (M.op X0 x)
       grind)
    | exact superpose eq107128 eq750
    | (have j1 := eq107128 X0
       grind)
    | exact resolve eq750 eq107128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107437 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq107128 eq107426
    | (have j0 := eq107426 X0
       have j1 := eq107128 X0
       grind)
    | exact resolve eq107426 eq107128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107426
  have eq107438 : ∀ X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) X2) ∨ (k X3 (M.op (σ x) (σ y))) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | (have i₁ := eq107425 x x X2 X3
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq107425
    | (have j0 := eq107425 x x X2 X3
       grind)
    | exact resolve eq107425 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107425
  have eq107447 : ∀ X2 X3 : G, (σ x) = (M.op (M.op (σ y) (σ x)) X2) ∨ (k X3 (M.op (σ x) (σ y))) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | exact superpose eq107437 eq107438
    | (have j0 := eq107438 X2 X3
       have j1 := eq107437 X3
       grind)
    | exact resolve eq107438 eq107437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107438
  have eq107454 : ∀ X2 X3 : G, (σ x) = (M.op (σ x) X2) ∨ (k X3 (M.op (σ x) (σ y))) = X3 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2 X3
    first
    | exact superpose eq107128 eq107447
    | (have j0 := eq107447 X2 X3
       have j1 := eq107128 X3
       grind)
    | exact resolve eq107447 eq107128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107128 eq107447
  have eq107639 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22109
       have i₂ := eq107437 (M.op sF2 sF4)
       grind)
    | exact superpose eq107437 eq22109
    | (have j1 := eq107437 X0
       grind)
    | exact resolve eq22109 eq107437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22109 eq107437
  have eq107724 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq107639
    | (have j0 := eq107639 X0
       grind)
    | exact resolve eq107639 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107639
  have eq108043 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107724 eq886
    | (have j0 := eq886 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq886 (M.op (σ x) (σ y))
       have r₂ := eq107724 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq886 eq107724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107724
  have eq108105 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq108043
  have eq108208 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108105 eq750
    | exact resolve eq750 eq108105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq108218 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108105 eq108208
    | exact resolve eq108208 eq108105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108105 eq108208
  have eq108424 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108218 eq80446
    | exact resolve eq80446 eq108218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108218
  have eq108462 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq108424
  have eq114332 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108462 eq80446
    | exact resolve eq80446 eq108462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80446 eq108462
  have eq114362 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq114332
  have eq114394 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq114362
    | exact resolve eq114362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114362
  have eq114395 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq114394
  have eq114514 : (M.op x y) = (τ (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114395 eq29
    | exact resolve eq29 eq114395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114395
  have eq114668 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq114514
    | exact resolve eq114514 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114514
  have eq114696 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114668 eq27
    | exact resolve eq27 eq114668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114668
  have eq115017 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq114696
       have r₂ := eq41704
       grind)
    | exact resolve eq114696 eq41704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114696
  have eq115100 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq115017
       grind)
    | exact superpose eq115017 eq18
    | exact resolve eq18 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115101 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq115017
       grind)
    | exact superpose eq115017 eq24
    | exact resolve eq24 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115017
  have eq115177 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq115101
    | exact resolve eq115101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115101
  have eq115178 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq769 eq115100
    | exact resolve eq115100 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115100
  have eq115418 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq115178 eq777
    | exact resolve eq777 eq115178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq115434 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq115178 eq1012
    | exact resolve eq1012 eq115178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq115505 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq115178 eq22059
    | exact resolve eq22059 eq115178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22059
  have eq115506 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq115178 eq22061
    | exact resolve eq22061 eq115178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115178
  have eq115576 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq115506
    | exact resolve eq115506 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115506
  have eq115577 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ (M.op x y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq20 eq115505
    | (have j0 := eq115505 X0
       grind)
    | exact resolve eq115505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115505
  have eq115645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq115434
    | exact resolve eq115434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115434
  have eq115659 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq115177 eq115577
    | exact resolve eq115577 eq115177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115577
  have eq115708 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq115177 eq115645
    | exact resolve eq115645 eq115177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115177 eq115645
  have eq115725 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq115659 eq115708
    | exact resolve eq115708 eq115659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115659 eq115708
  have eq116045 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq115725 eq26
    | exact resolve eq26 eq115725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115725
  have eq116245 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq115418 eq116045
    | exact resolve eq116045 eq115418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115418 eq116045
  have eq116494 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq116245 eq27
    | exact resolve eq27 eq116245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116245
  have eq116766 : x = (σ x) := by
    first
    | (have r₁ := eq116494
       have r₂ := eq115576
       grind)
    | exact resolve eq116494 eq115576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115576 eq116494
  have eq117513 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq18
    | exact resolve eq18 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq117514 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq22
    | exact resolve eq22 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq117536 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq769
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq769
    | exact resolve eq769 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq117595 : (M.op x y) ≠ (σ x) ∨ (σ x) = (k (σ x) y) := by
    first
    | (have i₁ := eq61386
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq61386
    | exact resolve eq61386 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61386
  have eq117596 : (k (σ x) (σ y)) = (k (σ x) y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq65585
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq65585
    | exact resolve eq65585 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65585
  have eq117788 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (σ x) (τ X0)) := by
    intro X0
    first
    | exact superpose eq117514 eq399
    | exact resolve eq399 eq117514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq118185 : y ≠ (M.op x y) ∨ (σ x) = (k (σ x) y) := by
    first
    | exact superpose eq117513 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq117513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq118188 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq117513 eq695
    | exact resolve eq695 eq117513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq118513 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq117536 eq22061
    | exact resolve eq22061 eq117536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22061
  have eq118535 : (k (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq117536 eq65413
    | exact resolve eq65413 eq117536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65413
  have eq125082 : (τ (σ x)) = (k (σ x) (τ (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq65544 eq117788
    | exact resolve eq117788 eq65544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65544 eq117788
  have eq125412 : (τ (σ x)) = (k (σ x) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq125082
    | exact resolve eq125082 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125082
  have eq125531 : x = (k (σ x) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq125412
    | exact resolve eq125412 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq125412
  have eq125605 : (σ x) = (k (σ x) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq125531
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq125531
    | exact resolve eq125531 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125531
  have eq125634 : (σ x) = (k (σ x) y) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq125605
       have r₂ := eq118185
       grind)
    | exact resolve eq125605 eq118185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118185 eq125605
  have eq129919 : (σ (σ x)) = (k (σ (σ x)) (σ y)) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq125634 eq41
    | exact resolve eq41 eq125634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq125634
  have eq129927 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq117514 eq129919
    | exact resolve eq129919 eq117514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117514 eq129919
  have eq152628 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq117513
       have i₂ := eq107454 x (M.op sF2 y)
       grind)
    | exact superpose eq107454 eq117513
    | (have j1 := eq107454 x X0
       grind)
    | exact resolve eq117513 eq107454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152667 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq107454 x (M.op sF2 sF3)
       grind)
    | exact superpose eq107454 eq26
    | (have j1 := eq107454 (σ y) X0
       grind)
    | exact resolve eq26 eq107454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107454
  have eq153348 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152667 eq886
    | (have j0 := eq886 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq886 (M.op (σ x) (σ y))
       have r₂ := eq152667 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq886 eq152667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152667
  have eq153412 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq153348
  have eq153542 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq153412 eq764
    | exact resolve eq764 eq153412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153546 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153412 eq118188
    | exact resolve eq118188 eq153412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153551 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153412 eq153546
    | exact resolve eq153546 eq153412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153546
  have eq153553 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq153542 x x X2
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq153542
    | exact resolve eq153542 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153542
  have eq153582 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq117536 eq153553
    | exact resolve eq153553 eq117536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153553
  have eq153601 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq153412 eq153582
    | exact resolve eq153582 eq153412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153412 eq153582
  have eq153612 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq153551 eq153601
    | exact resolve eq153601 eq153551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153551 eq153601
  have eq153985 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153612 eq88454
    | exact resolve eq88454 eq153612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88454 eq153612
  have eq154015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq153985
  have eq155772 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152628 eq886
    | (have j0 := eq886 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq886 (M.op (σ x) (σ y))
       have r₂ := eq152628 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq886 eq152628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq152628
  have eq155836 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq155772
  have eq156138 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq155836 eq764
    | exact resolve eq764 eq155836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq156142 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155836 eq118188
    | exact resolve eq118188 eq155836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118188
  have eq156147 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155836 eq156142
    | exact resolve eq156142 eq155836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156142
  have eq156149 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq156138 x x X2
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq156138
    | exact resolve eq156138 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq156138
  have eq156178 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq117536 eq156149
    | exact resolve eq156149 eq117536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156149
  have eq156198 : ∀ X2 : G, (M.op (σ x) (M.op x y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq155836 eq156178
    | exact resolve eq156178 eq155836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155836 eq156178
  have eq156210 : ∀ X2 : G, (M.op (σ x) (σ y)) = (M.op X2 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq156147 eq156198
    | exact resolve eq156198 eq156147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156198
  have eq156285 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq156147 eq118535
    | exact resolve eq118535 eq156147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118535 eq156147
  have eq156360 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq156285
       have r₂ := eq177
       grind)
    | exact resolve eq156285 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq156285
  have eq156380 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq129927 eq156360
    | exact resolve eq156360 eq129927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129927 eq156360
  have eq158454 : (M.op x y) = (σ x) ∨ x = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq156380 eq60154
    | exact resolve eq60154 eq156380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60154 eq156380
  have eq158466 : (M.op x y) = (σ x) ∨ x = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq158454
  have eq158474 : (σ x) = (k (σ x) y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq158466
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq158466
    | exact resolve eq158466 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158466
  have eq158488 : (σ x) = (k (σ x) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq158474
       have r₂ := eq117595
       grind)
    | exact resolve eq158474 eq117595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117595 eq158474
  have eq158513 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq158488 eq117596
    | exact resolve eq117596 eq158488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117596 eq158488
  have eq158523 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq158513
  have eq163342 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq154015 eq117536
    | exact resolve eq117536 eq154015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117536 eq154015
  have eq163371 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq163342
    | exact resolve eq163342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163342
  have eq163466 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88518 eq163371
    | exact resolve eq163371 eq88518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88518 eq163371
  have eq163467 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq163466
  have eq163682 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq163467 eq83347
    | exact resolve eq83347 eq163467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83347
  have eq163683 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq163467 eq83376
    | exact resolve eq83376 eq163467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83376
  have eq163733 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq163744 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq163683
  have eq163745 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq163682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163682
  have eq163765 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq163744
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq163744
    | exact resolve eq163744 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163744
  have eq163766 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq163745 X0
       have i₂ := eq116766
       grind)
    | exact superpose eq116766 eq163745
    | (have j0 := eq163745 X0
       grind)
    | exact resolve eq163745 eq116766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116766 eq163745
  have eq163850 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq163765
       have r₂ := eq163733
       grind)
    | exact resolve eq163765 eq163733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163765
  have eq163851 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq163766 X0
       grind)
    | (have r₁ := eq163766 X0
       have r₂ := eq163733
       grind)
    | exact resolve eq163766 eq163733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163766
  have eq163906 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq163850 eq163851
    | exact resolve eq163851 eq163850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163851
  have eq164093 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq163850 eq11
    | exact resolve eq11 eq163850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163850
  have eq164105 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq164093
  have eq164129 : (M.op x y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq164105
       have r₂ := eq163733
       grind)
    | exact resolve eq164105 eq163733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164105
  have eq164493 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq156210 eq163906
    | exact resolve eq163906 eq156210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156210 eq163906
  have eq164682 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq164493
  have eq164743 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq164682
       have r₂ := eq163733
       grind)
    | exact resolve eq164682 eq163733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164682
  have eq164795 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq163467 eq164743
    | exact resolve eq164743 eq163467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163467 eq164743
  have eq165638 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq164795 eq158523
    | exact resolve eq158523 eq164795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158523 eq164795
  have eq165645 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq165638
  have eq165658 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq164129 eq165645
    | exact resolve eq165645 eq164129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164129 eq165645
  have eq165765 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq165658
       have r₂ := eq163733
       grind)
    | exact resolve eq165658 eq163733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163733 eq165658
  have eq165862 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq165765 eq29
    | exact resolve eq29 eq165765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq165765
  have eq166061 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq165862
    | exact resolve eq165862 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq165862
  have eq166136 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166061 eq27
    | exact resolve eq27 eq166061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166061
  have eq166446 : y = (M.op x y) := by
    first
    | (have r₁ := eq166136
       have r₂ := eq41704
       grind)
    | exact resolve eq166136 eq41704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41704 eq166136
  have eq166507 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq166446
       grind)
    | exact superpose eq166446 eq24
    | exact resolve eq24 eq166446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq166562 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq117513
       have i₂ := eq166446
       grind)
    | exact superpose eq166446 eq117513
    | exact resolve eq117513 eq166446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117513 eq166446
  have eq167595 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq166562 eq118513
    | exact resolve eq118513 eq166562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118513
  have eq167653 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq167595 eq166507
    | exact resolve eq166507 eq167595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166507
  have eq167654 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq167595 eq20
    | exact resolve eq20 eq167595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq167595
  have eq168656 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq167653 eq26
    | exact resolve eq26 eq167653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq167653
  have eq168956 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq166562 eq168656
    | exact resolve eq168656 eq166562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166562 eq168656
  have eq169704 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq168956 eq27
    | exact resolve eq27 eq168956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq168956
  have eq169974 : False := by grind
  exact eq169974

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyy_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  clear eq19
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X0)) X0
       have i₂ := eq9 (M.op X0 (M.op X1 X0)) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq285 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
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
  clear eq32
  have eq4074 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq284
    | (have j0 := eq284 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq284 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13723 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq285 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq13724 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq13723 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq13749 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (M.op X1 X0)))) ≠ (τ (M.op X0 (M.op X0 (M.op X1 X0)))) ∨ (τ (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq13724 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq13724
    | (have j0 := eq13724 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact resolve eq13724 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq13759 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13724 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq13724
    | (have j0 := eq13724 (σ X0)
       grind)
    | exact resolve eq13724 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13724
  have eq13770 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq13749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13749
  have eq13781 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13759 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13759
    | (have j0 := eq13759 X0
       grind)
    | exact resolve eq13759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13759
  have eq13798 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13781 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13781
    | (have j0 := eq13781 X0
       grind)
    | exact resolve eq13781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781
  have eq16273 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0))))) (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0)))) X2
       have i₂ := eq13770 X0 X1
       grind)
    | exact superpose eq13770 eq63
    | exact resolve eq63 eq13770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16365 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16273 X0 X1 X2
       have i₂ := eq13770 X0 X1
       grind)
    | exact superpose eq13770 eq16273
    | exact resolve eq16273 eq13770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16273
  have eq16423 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16365 X0 X1 X2
       have i₂ := eq13770 X0 X1
       grind)
    | exact superpose eq13770 eq16365
    | exact resolve eq16365 eq13770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13770 eq16365
  have eq16530 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16423 (M.op X0 (M.op X1 X0)) X0 X2
       have i₂ := eq9 (M.op X0 (M.op X1 X0)) X0 X1
       grind)
    | exact superpose eq9 eq16423
    | exact resolve eq16423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq54505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4074 x y
       grind)
    | exact superpose eq4074 eq16
    | (have j1 := eq4074 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4074 x y
       grind)
    | exact resolve eq16 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54588 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq4074
  have eq54713 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq54588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54588
  have eq54721 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq54505
  have eq54732 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54713 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq54713
    | (have j0 := eq54713 X0
       grind)
    | exact resolve eq54713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54713
  have eq54769 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq54732
  have eq54824 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq54721
  have eq54952 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq54824
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq54824
    | exact resolve eq54824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54824
  have eq54966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq54952
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq54952 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54952
  have eq54975 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq54966
       have r₂ := eq16
       grind)
    | exact resolve eq54966 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54966
  have eq54989 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq54975
       grind)
    | exact superpose eq54975 eq9
    | exact resolve eq9 eq54975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55121 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ x)
       have i₂ := eq54989 (σ x)
       grind)
    | exact superpose eq54989 eq9
    | exact resolve eq9 eq54989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54989
  have eq55941 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq55121 (M.op (σ x) (σ x))
       grind)
    | exact superpose eq55121 eq66
    | exact resolve eq66 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq55948 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq54975
       have i₂ := eq55121 (σ y)
       grind)
    | exact superpose eq55121 eq54975
    | exact resolve eq54975 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54975
  have eq55993 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq55948
  have eq56041 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq55121 eq55941
    | exact resolve eq55941 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55121 eq55941
  have eq56085 : x = (k x x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq56041
    | exact resolve eq56041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56041
  have eq165993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54769 y
       have i₂ := eq55993
       grind)
    | exact superpose eq55993 eq54769
    | (have j0 := eq54769 y
       grind)
    | exact resolve eq54769 eq55993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54769 eq55993
  have eq166403 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq165993
       have r₂ := eq16
       grind)
    | exact resolve eq165993 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165993
  have eq166430 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) (σ y) x
       have i₂ := eq166403
       grind)
    | exact superpose eq166403 eq63
    | exact resolve eq63 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq166513 : ∀ X0 : G, (M.op X0 (τ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))))) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16530 (σ y) (σ y) x
       have i₂ := eq166403
       grind)
    | exact superpose eq166403 eq16530
    | exact resolve eq16530 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16530
  have eq166610 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq166403 eq166513
    | exact resolve eq166513 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166513
  have eq166693 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq166403 eq166430
    | exact resolve eq166430 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166430
  have eq166747 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq166403 eq166610
    | exact resolve eq166610 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166610
  have eq166830 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq166403 eq166693
    | exact resolve eq166693 eq166403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166403 eq166693
  have eq166870 : ∀ X0 : G, x = (M.op y x) ∨ x = y ∨ (M.op X0 y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq166747 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq166747
    | exact resolve eq166747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166747
  have eq167283 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166830 (σ x)
       grind)
    | exact superpose eq166830 eq16
    | exact resolve eq16 eq166830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166830
  have eq167507 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq166870 eq167283
    | exact resolve eq167283 eq166870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166870 eq167283
  have eq167508 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq167507
  have eq167612 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq167508
       grind)
    | exact superpose eq167508 eq9
    | exact resolve eq9 eq167508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167933 : ∀ X0 : G, (σ x) = (σ y) ∨ x = y ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq167612 x
       grind)
    | exact superpose eq167612 eq9
    | exact resolve eq9 eq167612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167612
  have eq168621 : ∀ X0 : G, y = (τ (σ x)) ∨ x = y ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq167933 X0
       grind)
    | exact superpose eq167933 eq10
    | (have j1 := eq167933 X0
       grind)
    | exact resolve eq10 eq167933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167933
  have eq168765 : ∀ X0 : G, x = y ∨ x = y ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq168621 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq168621
    | (have j0 := eq168621 X0
       grind)
    | exact resolve eq168621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168621
  have eq168766 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq168765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168765
  have eq169345 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq167508
       have i₂ := eq168766 y
       grind)
    | exact superpose eq168766 eq167508
    | exact resolve eq167508 eq168766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167508 eq168766
  have eq169346 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq169345
  have eq169570 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq169346
       grind)
    | exact superpose eq169346 eq10
    | exact resolve eq10 eq169346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169346
  have eq169721 : x = y ∨ x = y := by
    first
    | (have i₁ := eq169570
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq169570
    | exact resolve eq169570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169570
  have eq169722 : x = y := by grind
  clear eq169721
  have eq169724 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169722
       grind)
    | exact superpose eq169722 eq16
    | exact resolve eq16 eq169722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169774 : x = (M.op x x) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56085
       have i₂ := eq169722
       grind)
    | exact superpose eq169722 eq56085
    | exact resolve eq56085 eq169722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56085
  have eq169895 : x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13798 x
       grind)
    | (have r₁ := eq169774
       have r₂ := eq13798 x
       grind)
    | exact resolve eq169774 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13798 eq169774
  have eq169994 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq169895
       have i₂ := eq169722
       grind)
    | exact superpose eq169722 eq169895
    | exact resolve eq169895 eq169722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169722 eq169895
  have eq169995 : x = (M.op x x) := by grind
  clear eq169994
  have eq169996 : (M.op x x) = (k x x) := by grind
  have eq170267 : x = (k x x) := by
    first
    | (have i₁ := eq169996
       have i₂ := eq169995
       grind)
    | exact superpose eq169995 eq169996
    | exact resolve eq169996 eq169995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169996
  have eq170444 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq284 x x
       have i₂ := eq170267
       grind)
    | exact superpose eq170267 eq284
    | (have j0 := eq284 x x
       grind)
    | exact resolve eq284 eq170267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq170267
  have eq170447 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq170444
  have eq170458 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq170447
  have eq170472 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq170458
  have eq170473 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq169724
       have i₂ := eq169995
       grind)
    | exact superpose eq169995 eq169724
    | exact resolve eq169724 eq169995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169724 eq169995
  have eq170474 : False := by grind
  exact eq170474

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ (M.op X0 (M.op X0 (M.op X1 X0))) ∨ (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X2 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 (M.op X2 X1))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq56 (τ X1) X0
       grind)
    | exact superpose eq56 eq17
    | (have j1 := eq56 (τ X1) X0
       grind)
    | exact resolve eq17 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq105 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq241 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq264 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq271 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq264 X0 X0
       grind)
    | exact superpose eq264 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq264 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq264 X1 X1
       grind)
    | exact resolve eq12 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq105
    | (have j1 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq105 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq344 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq343
  have eq349 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq344
       grind)
    | exact superpose eq344 eq9
    | exact resolve eq9 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq1106 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq292 X0 X1
       grind)
    | exact superpose eq292 eq10
    | (have j1 := eq292 X0 X1
       grind)
    | exact resolve eq10 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq1146 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1106
    | (have j0 := eq1106 X0 X0
       grind)
    | exact resolve eq1106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1211 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1146 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1212 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1211 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1278 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1212 (σ X0)
       grind)
    | exact superpose eq1212 eq15
    | exact resolve eq15 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq1212 (τ X0)
       grind)
    | exact superpose eq1212 eq35
    | exact resolve eq35 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1291 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1284 X0
       have i₂ := eq1212 X0
       grind)
    | exact superpose eq1212 eq1284
    | exact resolve eq1284 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1297 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1278 X0
       have i₂ := eq1212 X0
       grind)
    | exact superpose eq1212 eq1278
    | exact resolve eq1278 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq1278
  have eq1405 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq1291 X0
       grind)
    | exact superpose eq1291 eq9
    | exact resolve eq9 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq1297 X0
       grind)
    | exact superpose eq1297 eq9
    | exact resolve eq9 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3257 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1451 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq1451
    | exact resolve eq1451 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3394 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3257 X0 X1 X2
       have i₂ := eq1297 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq1297 eq3257
    | exact resolve eq3257 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq3421 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3394 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq3394
    | exact resolve eq3394 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394
  have eq3443 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3421 X0 X1 X2
       have i₂ := eq1297 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq1297 eq3421
    | exact resolve eq3421 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3460 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3443 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq3443
    | exact resolve eq3443 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq14056 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq349 X1
       grind)
    | exact superpose eq349 eq9
    | (have j1 := eq349 X1
       grind)
    | exact resolve eq9 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq14128 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ (M.op x x)))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14056 X0 X1
       have i₂ := eq1297 x
       grind)
    | exact superpose eq1297 eq14056
    | (have j0 := eq14056 X0 X1
       grind)
    | exact resolve eq14056 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14056
  have eq274506 : ∀ X0 X1 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1451 x X0
       have i₂ := eq14128 (σ x) X1
       grind)
    | exact superpose eq14128 eq1451
    | (have j1 := eq14128 X0 X1
       grind)
    | exact resolve eq1451 eq14128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq14128
  have eq275501 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ x)) (M.op (τ (σ x)) (τ (σ x))))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1405 (σ x) X0
       have i₂ := eq274506 (σ x) X1
       grind)
    | exact superpose eq274506 eq1405
    | (have j1 := eq274506 X0 X1
       grind)
    | exact resolve eq1405 eq274506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405 eq274506
  have eq276098 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ x)) (τ (M.op (σ x) (σ x))))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq275501 X0 X1
       have i₂ := eq1291 (σ x)
       grind)
    | exact superpose eq1291 eq275501
    | (have j0 := eq275501 X0 X1
       grind)
    | exact resolve eq275501 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq275501
  have eq276173 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ x)) (τ (σ (M.op x x))))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276098 X0 X1
       have i₂ := eq1297 x
       grind)
    | exact superpose eq1297 eq276098
    | (have j0 := eq276098 X0 X1
       grind)
    | exact resolve eq276098 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276098
  have eq276199 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ x)) (M.op x x))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276173 X0 X1
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq276173
    | (have j0 := eq276173 X0 X1
       grind)
    | exact resolve eq276173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276173
  have eq276220 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (M.op X1 (M.op x (M.op x x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276199 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq276199
    | (have j0 := eq276199 X0 X0
       grind)
    | exact resolve eq276199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276199
  have eq286535 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have j0 := eq276220 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276220
  have eq286536 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 := by
    intro X0
    first
    | (have j0 := eq286535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286535
  have eq286760 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq34 x x x
       have i₂ := eq286536 x
       grind)
    | exact superpose eq286536 eq34
    | exact resolve eq34 eq286536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq286821 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3460 x x X0
       have i₂ := eq286536 x
       grind)
    | exact superpose eq286536 eq3460
    | exact resolve eq3460 eq286536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460 eq286536
  have eq297451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq286760 y
       grind)
    | exact superpose eq286760 eq105
    | exact resolve eq105 eq286760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq286760
  have eq297452 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq297451
  have eq297453 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq297452
       have i₂ := eq286821 (σ y)
       grind)
    | exact superpose eq286821 eq297452
    | exact resolve eq297452 eq286821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286821 eq297452
  have eq298947 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq297453
       grind)
    | exact superpose eq297453 eq10
    | exact resolve eq10 eq297453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297453
  have eq299311 : x = y := by
    first
    | (have i₁ := eq298947
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq298947
    | exact resolve eq298947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298947
  have eq300654 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299311
       grind)
    | exact superpose eq299311 eq16
    | exact resolve eq16 eq299311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299311
  have eq300681 : False := by grind
  exact eq300681

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
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
  have eq220 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq221 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq208 eq220
    | exact resolve eq220 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq223 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq14
    | exact resolve eq14 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq223 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq223
    | exact resolve eq223 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq226 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq208 eq224
    | exact resolve eq224 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq249 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq381 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq399 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq381
    | exact resolve eq381 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq472 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq50
    | exact resolve eq50 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq473 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq472 X2 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq472
    | exact resolve eq472 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq486 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq473 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq473 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq501 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
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
  have eq502 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq208 eq501
    | exact resolve eq501 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq503 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq502 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq502
    | exact resolve eq502 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq502
  have eq504 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq208 eq503
    | exact resolve eq503 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq503
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X0 X1 X2
       have i₂ := eq490 X0
       grind)
    | exact superpose eq490 eq14
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq543 X0 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq543
    | exact resolve eq543 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq76 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq607 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq602 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq611 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq607 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq607 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq3369 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq490 eq611
    | (have j0 := eq611 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq611 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq3385 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq473 eq3369
    | (have j0 := eq3369 X0
       grind)
    | exact resolve eq3369 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3386 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3385 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3416 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3386 eq249
    | exact resolve eq249 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq3421 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3386 eq35
    | exact resolve eq35 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3422 : (M.op (σ y) (σ y)) = (σ (k y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3386 eq36
    | exact resolve eq36 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3386
  have eq3446 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq490 eq3422
    | exact resolve eq3422 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3447 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq490 eq3421
    | exact resolve eq3421 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3469 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3446
       grind)
    | exact superpose eq3446 eq16
    | exact resolve eq16 eq3446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3490 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq16
    | exact resolve eq16 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3643 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq77
    | (have j0 := eq77 x
       grind)
    | exact resolve eq77 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq3652 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3643
  have eq3660 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3652
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3652
    | exact resolve eq3652 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3652
  have eq3744 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3660
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq3660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq3750 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3744 eq49
    | exact resolve eq49 eq3744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3744
  have eq3870 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78
    | (have j0 := eq78 y
       grind)
    | exact resolve eq78 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3878 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3870
  have eq3885 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3878
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq3878
    | exact resolve eq3878 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3878
  have eq3970 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3885
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq3885 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3991 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3970 eq104
    | exact resolve eq104 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq3970
  have eq4026 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq3991 eq3469
    | exact resolve eq3469 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469
  have eq4054 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq3750 eq3490
    | exact resolve eq3490 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq4125 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq490 eq3416
    | exact resolve eq3416 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq4130 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3416 eq548
    | exact resolve eq548 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq3416
  have eq4211 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4125 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4125
    | exact resolve eq4125 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4616 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq4211 X0
       grind)
    | exact superpose eq4211 eq15
    | exact resolve eq15 eq4211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4940 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1 X2
       have i₂ := eq4616 X0
       grind)
    | exact superpose eq4616 eq14
    | exact resolve eq14 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4940 X0 x x
       have i₂ := eq399 x x
       grind)
    | exact superpose eq399 eq4940
    | exact resolve eq4940 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq5300 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq504 eq4130
    | exact resolve eq4130 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq5327 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq5300
       have i₂ := eq4125 (M.op x sF0)
       grind)
    | exact superpose eq4125 eq5300
    | exact resolve eq5300 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125 eq5300
  have eq5349 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq504 eq5327
    | exact resolve eq5327 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327
  have eq5368 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq5349 eq15
    | exact resolve eq15 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq28516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq28515
    | exact resolve eq28515 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28515
  have eq28527 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq28516
       have r₂ := eq27
       grind)
    | exact resolve eq28516 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28516
  have eq28531 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28527 eq3991
    | exact resolve eq3991 eq28527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991 eq28527
  have eq28573 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28531
       have i₂ := eq4026
       grind)
    | exact superpose eq4026 eq28531
    | exact resolve eq28531 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026 eq28531
  have eq28581 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq28573
    | exact resolve eq28573 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28573
  have eq28582 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28581
  have eq28589 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28582 eq3750
    | exact resolve eq3750 eq28582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750 eq28582
  have eq28631 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28589
       have i₂ := eq4054
       grind)
    | exact superpose eq4054 eq28589
    | exact resolve eq28589 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4054 eq28589
  have eq28639 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq28631
    | exact resolve eq28631 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28631
  have eq28640 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq28639
  have eq28664 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq399 y y
       have i₂ := eq28640
       grind)
    | exact superpose eq28640 eq399
    | exact resolve eq399 eq28640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29082 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28640
       have i₂ := eq28664
       grind)
    | exact superpose eq28664 eq28640
    | exact resolve eq28640 eq28664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28640 eq28664
  have eq29096 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq29082
  have eq29126 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29096 eq473
    | exact resolve eq473 eq29096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29142 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29096 eq5368
    | exact resolve eq5368 eq29096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29096
  have eq29180 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29142
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29142
    | exact resolve eq29142 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29142
  have eq29522 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3447
       have i₂ := eq29180
       grind)
    | exact superpose eq29180 eq3447
    | exact resolve eq3447 eq29180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29536 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq4943 x
       have i₂ := eq29180
       grind)
    | exact superpose eq29180 eq4943
    | exact resolve eq4943 eq29180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29539 : (M.op x x) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq399 x x
       have i₂ := eq29180
       grind)
    | exact superpose eq29180 eq399
    | exact resolve eq399 eq29180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29552 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29536
       have i₂ := eq4616 x
       grind)
    | exact superpose eq4616 eq29536
    | exact resolve eq29536 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29536
  have eq29564 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29522
    | exact resolve eq29522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29522
  have eq29568 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29552
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq29552
    | exact resolve eq29552 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29552
  have eq29762 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29126 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29126
    | (have j0 := eq29126 x
       grind)
    | exact resolve eq29126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29126
  have eq29835 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3447
       have i₂ := eq29762
       grind)
    | exact superpose eq29762 eq3447
    | exact resolve eq3447 eq29762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29849 : (M.op x (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4943 x
       have i₂ := eq29762
       grind)
    | exact superpose eq29762 eq4943
    | exact resolve eq4943 eq29762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq29852 : (M.op x x) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq399 x x
       have i₂ := eq29762
       grind)
    | exact superpose eq29762 eq399
    | exact resolve eq399 eq29762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq29865 : (σ (M.op x x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29849
       have i₂ := eq4616 x
       grind)
    | exact superpose eq4616 eq29849
    | exact resolve eq29849 eq4616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616 eq29849
  have eq29877 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29835
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29835
    | exact resolve eq29835 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29835
  have eq29881 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29865
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq29865
    | exact resolve eq29865 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447 eq29865
  have eq31208 : (σ x) = (M.op x (M.op x y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq29568 eq29564
    | exact resolve eq29564 eq29568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29564 eq29568
  have eq31226 : (σ x) = (M.op x (M.op x y)) ∨ y = (σ y) := by grind
  clear eq31208
  have eq31262 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31226 eq226
    | exact resolve eq226 eq31226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31278 : (σ x) = (τ (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq31226 eq5349
    | exact resolve eq5349 eq31226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31226
  have eq31323 : y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq31278
    | exact resolve eq31278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31278
  have eq31326 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq31262
    | exact resolve eq31262 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31262
  have eq31329 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (σ x) := by
    first
    | exact superpose eq31323 eq26
    | exact resolve eq26 eq31323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31415 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq31326 eq221
    | exact resolve eq221 eq31326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31326
  have eq31417 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq31415
    | exact resolve eq31415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31415
  have eq31890 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq31417 eq29539
    | exact resolve eq29539 eq31417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29539 eq31417
  have eq31898 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (σ y) := by grind
  clear eq31890
  have eq32231 : x = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29180
       have i₂ := eq31898
       grind)
    | exact superpose eq31898 eq29180
    | exact resolve eq29180 eq31898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29180 eq31898
  have eq32250 : y = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq32231
  have eq32261 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32250 eq26
    | exact resolve eq26 eq32250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32250
  have eq38340 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29881 eq29877
    | exact resolve eq29877 eq29881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29877 eq29881
  have eq38360 : (σ x) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq38340
  have eq38401 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38360 eq226
    | exact resolve eq226 eq38360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq38417 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38360 eq5349
    | exact resolve eq5349 eq38360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349 eq38360
  have eq38467 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq38417
    | exact resolve eq38417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq38417
  have eq38470 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq38401
    | exact resolve eq38401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38401
  have eq38828 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq38467 eq20
    | exact resolve eq20 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38883 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38467 eq473
    | exact resolve eq473 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq39025 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq38883 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38883
    | (have j0 := eq38883 X0
       grind)
    | exact resolve eq38883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38883
  have eq39079 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq38828
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38828
    | exact resolve eq38828 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38828
  have eq39129 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38470 eq221
    | exact resolve eq221 eq38470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38470
  have eq39146 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq39129
    | exact resolve eq39129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39129
  have eq39226 : y = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq39079 eq31323
    | exact resolve eq31323 eq39079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31323 eq39079
  have eq39229 : y = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq39226
  have eq42235 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq38467 eq39025
    | exact resolve eq39025 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38467 eq39025
  have eq42341 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq42235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42235
  have eq42849 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39146 eq29852
    | exact resolve eq29852 eq39146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29852 eq39146
  have eq42862 : (M.op (σ x) (σ y)) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq42849
  have eq45059 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq31329
       have i₂ := eq42341 sF2
       grind)
    | exact superpose eq42341 eq31329
    | exact resolve eq31329 eq42341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31329 eq42341
  have eq45063 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq45059
  have eq45466 : y ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq45063 eq27
    | exact resolve eq27 eq45063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45063
  have eq45488 : x = (σ x) := by
    first
    | (have r₁ := eq45466
       have r₂ := eq39229
       grind)
    | exact resolve eq45466 eq39229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39229 eq45466
  have eq45489 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq45488 eq26
    | exact resolve eq26 eq45488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq45577 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45488 eq32261
    | exact resolve eq32261 eq45488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32261
  have eq45592 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45577
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45577
    | exact resolve eq45577 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45577
  have eq46218 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45592 eq27
    | exact resolve eq27 eq45592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45592
  have eq47797 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29762
       have i₂ := eq42862
       grind)
    | exact superpose eq42862 eq29762
    | exact resolve eq29762 eq42862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29762 eq42862
  have eq47818 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq47797
  have eq47952 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47818 eq5368
    | exact resolve eq5368 eq47818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5368 eq47818
  have eq48020 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47952
    | exact resolve eq47952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47952
  have eq48131 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq48020
    | exact resolve eq48020 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48020
  have eq48197 : x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq48131
       have r₂ := eq46218
       grind)
    | exact resolve eq48131 eq46218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46218 eq48131
  have eq48698 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq48197 eq27
    | exact resolve eq27 eq48197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq48699 : (M.op x (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq48197 eq221
    | exact resolve eq221 eq48197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq48730 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq45489 eq48699
    | exact resolve eq48699 eq45489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45489 eq48699
  have eq48731 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq48197 eq48730
    | exact resolve eq48730 eq48197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48197 eq48730
  have eq48753 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq48731 eq504
    | exact resolve eq504 eq48731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq48731
  have eq49501 : x = (M.op x y) := by
    first
    | (have i₁ := eq48753 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48753
    | (have j0 := eq48753 y
       grind)
    | exact resolve eq48753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48753
  have eq49718 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq49501 eq20
    | exact resolve eq20 eq49501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq49501
  have eq50002 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49718
    | exact resolve eq49718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49718
  have eq50099 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq45488 eq50002
    | exact resolve eq50002 eq45488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45488 eq50002
  have eq50160 : False := by grind
  exact eq50160

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq35
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
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
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
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq185 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq182 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq186 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op X0 x)
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq179 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X2 X3
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq238 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq214 eq185
    | exact resolve eq185 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq185 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq185 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq251 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq214 eq250
    | exact resolve eq250 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq315 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq192 X0 X0
       have i₂ := eq251 X0
       grind)
    | exact superpose eq251 eq192
    | exact resolve eq192 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : (k (σ y) (σ (M.op (M.op x y) y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq251 eq36
    | exact resolve eq36 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq326 : (k (σ (M.op x y)) (σ (M.op (M.op x y) y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq251 eq37
    | exact resolve eq37 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq335 : (k x (τ (M.op (M.op x y) y))) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq251 eq90
    | exact resolve eq90 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq346 : (k y (τ (M.op (M.op x y) y))) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq251 eq107
    | exact resolve eq107 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1235 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1237 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1284 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq2593 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq40
    | exact resolve eq40 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1235
  have eq2594 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2593
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2593
    | exact resolve eq2593 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq2596 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2594
    | exact resolve eq2594 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2596 eq1237
    | exact resolve eq1237 eq2596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq2596
  have eq2611 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2604
       have r₂ := eq27
       grind)
    | exact resolve eq2604 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq2628 : (M.op (M.op x y) y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2611 eq192
    | exact resolve eq192 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2636 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2611 eq2628
    | exact resolve eq2628 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2682 : (τ (M.op (σ y) (σ y))) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2636 eq346
    | exact resolve eq346 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq2636
  have eq2717 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq2682
    | exact resolve eq2682 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2737 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2611 eq2717
    | exact resolve eq2717 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611 eq2717
  have eq2748 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq2737
    | exact resolve eq2737 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2750 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1286 y
       grind)
    | (have r₁ := eq2748
       have r₂ := eq1286 y
       grind)
    | exact resolve eq2748 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2753 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2750
       grind)
    | exact resolve eq13 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 y y X2 X0 X1
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq174
    | exact resolve eq174 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2765 : (M.op (M.op x y) y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq192 y y
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq192
    | exact resolve eq192 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq194 X0 y y
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq194
    | exact resolve eq194 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq2769 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2772 : (M.op (M.op x y) y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq186 eq2766
    | exact resolve eq2766 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq2766
  have eq2773 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2750 eq2765
    | exact resolve eq2765 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq2783 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq2755 x x X2
       have i₂ := eq192 x x
       grind)
    | (have i₁ := eq2755 x y X2
       have i₂ := eq192 X2 x
       grind)
    | exact superpose eq192 eq2755
    | (have j0 := eq2755 x y X2
       grind)
    | exact resolve eq2755 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755
  have eq2785 : (k y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2769 eq2772
    | exact resolve eq2772 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772
  have eq2793 : ∀ X2 : G, y = (M.op X2 (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2773 eq2783
    | exact resolve eq2783 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2795 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2773 eq2785
    | exact resolve eq2785 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785
  have eq2799 : ∀ X2 : G, y = (M.op X2 (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2769 eq2793
    | exact resolve eq2793 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793
  have eq2802 : ∀ X2 : G, y = (M.op X2 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2795 eq2799
    | exact resolve eq2799 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795 eq2799
  have eq2817 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2773 eq325
    | exact resolve eq325 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq2855 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2817
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2817
    | exact resolve eq2817 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817
  have eq2869 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2750 eq2855
    | exact resolve eq2855 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750 eq2855
  have eq2879 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2869
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2869
    | exact resolve eq2869 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2869
  have eq2935 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2802 x
       grind)
    | exact superpose eq2802 eq18
    | (have j1 := eq2802 x
       grind)
    | exact resolve eq18 eq2802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802
  have eq3037 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2935 eq185
    | exact resolve eq185 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3038 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2935 eq190
    | exact resolve eq190 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3041 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2935 eq214
    | exact resolve eq214 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3044 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3041
    | exact resolve eq3041 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq3047 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq3037
    | (have j0 := eq3037 X0
       grind)
    | exact resolve eq3037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037
  have eq3050 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2935 eq3044
    | exact resolve eq3044 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3053 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2935 eq3047
    | exact resolve eq3047 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3155 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2879 eq1286
    | (have j0 := eq1286 (σ y)
       grind)
    | (have r₁ := eq1286 (σ y)
       have r₂ := eq2879
       grind)
    | exact resolve eq1286 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq2879
  have eq3156 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3155
  have eq3209 : (τ (M.op (σ x) (σ x))) = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3050 eq335
    | exact resolve eq335 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3252 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3209
    | exact resolve eq3209 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3209
  have eq3268 : (k x x) = (τ (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3038 eq3252
    | exact resolve eq3252 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038 eq3252
  have eq3274 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3050 eq3268
    | exact resolve eq3268 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3275 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3274
    | exact resolve eq3274 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3374 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3156 eq174
    | exact resolve eq174 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3384 : (M.op (M.op x y) y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3156 eq192
    | exact resolve eq192 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3392 : (M.op (M.op x y) y) = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2769 eq3384
    | exact resolve eq3384 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3402 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq3374 x x X2
       have i₂ := eq192 x x
       grind)
    | (have i₁ := eq3374 x y X2
       have i₂ := eq192 X2 x
       grind)
    | exact superpose eq192 eq3374
    | (have j0 := eq3374 x y X2
       grind)
    | exact resolve eq3374 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq3405 : y = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2773 eq3392
    | exact resolve eq3392 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3414 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (k (σ y) y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2769 eq3402
    | exact resolve eq3402 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3402
  have eq3417 : (M.op x y) = (k (σ y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2935 eq3405
    | exact resolve eq3405 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3425 : ∀ X2 : G, y = (M.op X2 (k (σ y) y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2773 eq3414
    | exact resolve eq3414 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414
  have eq3434 : ∀ X2 : G, (M.op x y) = (M.op X2 (k (σ y) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq2935 eq3425
    | exact resolve eq3425 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq3439 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq3417 eq3434
    | exact resolve eq3434 eq3417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3434
  have eq3586 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1284 x x
       have i₂ := eq3275
       grind)
    | exact superpose eq3275 eq1284
    | (have j0 := eq1284 x x
       grind)
    | (have r₁ := eq1284 x x
       have r₂ := eq3275
       grind)
    | exact resolve eq1284 eq3275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3587 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3586
  have eq3588 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3587
  have eq3631 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3439 eq192
    | exact resolve eq192 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3671 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2769 eq3631
    | exact resolve eq3631 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3709 : y = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2773 eq3671
    | exact resolve eq3671 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq3735 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2935 eq3709
    | exact resolve eq3709 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq3776 : (M.op (M.op x y) y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq192 x x
       have i₂ := eq3588
       grind)
    | exact superpose eq3588 eq192
    | exact resolve eq192 eq3588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3784 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3050 eq3776
    | exact resolve eq3776 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3050 eq3776
  have eq3813 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3735 eq41
    | exact resolve eq41 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3735
  have eq3821 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3813
    | exact resolve eq3813 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq3825 : x = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3588
       have i₂ := eq3784
       grind)
    | exact superpose eq3784 eq3588
    | exact resolve eq3588 eq3784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588 eq3784
  have eq3845 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq3825
  have eq3874 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3845
       grind)
    | exact superpose eq3845 eq18
    | exact resolve eq18 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3916 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq189 eq3874
    | exact resolve eq3874 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq3874
  have eq3920 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq3845 eq3916
    | exact resolve eq3916 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq3951 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3821 eq1284
    | (have j0 := eq1284 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq1284 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq3821
       grind)
    | exact resolve eq1284 eq3821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq3952 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3951
  have eq3953 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3952
  have eq3976 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3953 eq192
    | exact resolve eq192 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3985 : (M.op (M.op x y) y) = (k (σ (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2769 eq3976
    | exact resolve eq3976 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq3999 : y = (k (σ (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2773 eq3985
    | exact resolve eq3985 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq3985
  have eq4012 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2935 eq3999
    | exact resolve eq3999 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq4161 : (σ (M.op x y)) = (k (σ (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3953
       have i₂ := eq2769 sF1
       grind)
    | exact superpose eq2769 eq3953
    | exact resolve eq3953 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq4163 : (σ y) = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3156
       have i₂ := eq2769 sF3
       grind)
    | exact superpose eq2769 eq3156
    | exact resolve eq3156 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769 eq3156
  have eq4166 : (σ y) = (k (σ y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4163
  have eq4168 : (σ (M.op x y)) = (k (σ (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4161
  have eq4191 : (σ y) = (k (σ y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2935 eq4166
    | exact resolve eq4166 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq4192 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2935 eq4168
    | exact resolve eq4168 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935 eq4168
  have eq4239 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq3417 eq4191
    | exact resolve eq4191 eq3417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417 eq4191
  have eq4240 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq4012 eq4192
    | exact resolve eq4192 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012 eq4192
  have eq4287 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq4239 eq185
    | exact resolve eq185 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4288 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4239 eq190
    | exact resolve eq190 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq4291 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4239 eq214
    | exact resolve eq214 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4294 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq4291
    | exact resolve eq4291 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291
  have eq4297 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq4287
    | (have j0 := eq4287 X0
       grind)
    | exact resolve eq4287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4287
  have eq4300 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4239 eq4294
    | exact resolve eq4294 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4294
  have eq4303 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq4239 eq4297
    | exact resolve eq4297 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239 eq4297
  have eq4312 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4240 eq185
    | exact resolve eq185 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4322 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq4312
    | (have j0 := eq4312 X0
       grind)
    | exact resolve eq4312 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4312
  have eq4328 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4240 eq4322
    | exact resolve eq4322 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240 eq4322
  have eq4354 : (τ (M.op (σ x) (σ x))) = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4300 eq335
    | exact resolve eq335 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq4398 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq4354
    | exact resolve eq4354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4354
  have eq4415 : (k x x) = (τ (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4288 eq4398
    | exact resolve eq4398 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288 eq4398
  have eq4421 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4300 eq4415
    | exact resolve eq4415 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415
  have eq4422 : x = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq4421
    | exact resolve eq4421 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4421
  have eq4722 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq1284 x x
       have i₂ := eq4422
       grind)
    | exact superpose eq4422 eq1284
    | (have j0 := eq1284 x x
       grind)
    | (have r₁ := eq1284 x x
       have r₂ := eq4422
       grind)
    | exact resolve eq1284 eq4422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq4723 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq4722
  have eq4724 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq4723
  have eq4747 : (M.op (M.op x y) y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq192 x x
       have i₂ := eq4724
       grind)
    | exact superpose eq4724 eq192
    | exact resolve eq192 eq4724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq4759 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4300 eq4747
    | exact resolve eq4747 eq4300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300 eq4747
  have eq4826 : x = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq4724
       have i₂ := eq4759
       grind)
    | exact superpose eq4759 eq4724
    | exact resolve eq4724 eq4759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724 eq4759
  have eq4850 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq4826
  have eq4882 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4850 eq26
    | exact resolve eq26 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4883 : y = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4850 eq31
    | exact resolve eq31 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4850
  have eq4929 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq3845 eq4883
    | exact resolve eq4883 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883
  have eq4954 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4929 eq14
    | exact resolve eq14 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq4955 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq4954
    | exact resolve eq4954 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4954
  have eq5215 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq4882 eq3439
    | exact resolve eq3439 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439 eq4882
  have eq5233 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq5215
  have eq5553 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq5233 eq214
    | exact resolve eq214 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq5557 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  have eq5562 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq26 eq5553
    | exact resolve eq5553 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5553
  have eq5571 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq5233 eq5562
    | exact resolve eq5562 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5233 eq5562
  have eq5579 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq3845 eq5571
    | exact resolve eq5571 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845 eq5571
  have eq5584 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq3920 eq5579
    | exact resolve eq5579 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920 eq5579
  have eq5588 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq5584
       have r₂ := eq5557
       grind)
    | exact resolve eq5584 eq5557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557 eq5584
  have eq5595 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq5588 eq27
    | exact resolve eq27 eq5588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq5624 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5595
       have r₂ := eq4955
       grind)
    | exact resolve eq5595 eq4955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955 eq5595
  have eq5631 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5624
       grind)
    | exact superpose eq5624 eq18
    | exact resolve eq18 eq5624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5645 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq5624
  have eq5682 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5631 eq4328
    | exact resolve eq4328 eq5631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328
  have eq5683 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5631 eq4303
    | exact resolve eq4303 eq5631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq5684 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5631 eq3053
    | exact resolve eq3053 eq5631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053
  have eq5703 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5684
  have eq5704 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq5683
  have eq5705 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq5682
  have eq5716 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5703
       have r₂ := eq5645
       grind)
    | exact resolve eq5703 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq5717 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5704
       have r₂ := eq5645
       grind)
    | exact resolve eq5704 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq5718 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5705
       have r₂ := eq5645
       grind)
    | exact resolve eq5705 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645 eq5705
  have eq5754 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5631
       have i₂ := eq5716
       grind)
    | exact superpose eq5716 eq5631
    | exact resolve eq5631 eq5716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5631 eq5716
  have eq5755 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5754
  have eq5787 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5717 eq26
    | exact resolve eq26 eq5717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq5835 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5755 eq5787
    | exact resolve eq5787 eq5755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755 eq5787
  have eq5916 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5835 eq27
    | exact resolve eq27 eq5835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5835
  have eq5943 : x = (M.op x y) := by
    first
    | (have r₁ := eq5916
       have r₂ := eq5718
       grind)
    | exact resolve eq5916 eq5718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718 eq5916
  have eq6037 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5943
       grind)
    | exact superpose eq5943 eq18
    | exact resolve eq18 eq5943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6038 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5943
       grind)
    | exact superpose eq5943 eq22
    | exact resolve eq22 eq5943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5943
  have eq6048 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6038 eq20
    | exact resolve eq20 eq6038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6038
  have eq6156 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq6037 eq238
    | exact resolve eq238 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq6157 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6037 eq251
    | exact resolve eq251 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq6158 : ∀ X0 : G, (M.op x y) = (M.op (k X0 (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq6037 eq315
    | exact resolve eq315 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq6163 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq6037 eq326
    | exact resolve eq326 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq6178 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6037 eq179
    | exact resolve eq179 eq6037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq6037
  have eq6196 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6178 eq6163
    | exact resolve eq6163 eq6178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163 eq6178
  have eq6203 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6196
    | exact resolve eq6196 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6196
  have eq6206 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6048 eq6203
    | exact resolve eq6203 eq6048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq6529 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6206 eq1284
    | (have j0 := eq1284 (σ x) (σ x)
       grind)
    | (have r₁ := eq1284 (σ x) (σ x)
       have r₂ := eq6206
       grind)
    | exact resolve eq1284 eq6206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq6206
  have eq6530 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6529
  have eq6531 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6530
  have eq6534 : (σ x) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq6531
       have i₂ := eq6157 sF2
       grind)
    | exact superpose eq6157 eq6531
    | exact resolve eq6531 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6531
  have eq6921 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6534 eq6158
    | exact resolve eq6158 eq6534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6158
  have eq6978 : (M.op x y) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq6921
       have i₂ := eq6157 sF2
       grind)
    | exact superpose eq6157 eq6921
    | exact resolve eq6921 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157 eq6921
  have eq6992 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq6978 eq6534
    | exact resolve eq6534 eq6978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534 eq6978
  have eq7004 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq6992 eq26
    | exact resolve eq26 eq6992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7058 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6156 eq7004
    | exact resolve eq7004 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156 eq7004
  have eq7087 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7058 eq27
    | exact resolve eq27 eq7058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7058
  have eq7109 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq6048 eq7087
    | exact resolve eq7087 eq6048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048 eq7087
  have eq7113 : False := by grind
  exact eq7113
