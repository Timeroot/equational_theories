import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq183 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq191 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq197 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq690 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq197
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq720 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq690
  have eq722 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq720
    | exact resolve eq720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq783 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq722 (τ X0) X1
       grind)
    | exact superpose eq722 eq18
    | (have j1 := eq722 (τ X0) X1
       grind)
    | exact resolve eq18 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq722
  have eq984 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq783 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq783
    | exact resolve eq783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq1030 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq984 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq984
    | (have j0 := eq984 X0 X1
       grind)
    | exact resolve eq984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq698
       have i₂ := eq1030 x y
       grind)
    | exact superpose eq1030 eq698
    | (have j1 := eq1030 (σ x) (σ y)
       grind)
    | (have r₁ := eq698
       have r₂ := eq1030 x y
       grind)
    | exact resolve eq698 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1151 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1150
  have eq1265 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1151
  have eq1564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq698
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq698
    | exact resolve eq698 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq1265
  have eq1565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1564
  have eq1566 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1565
  have eq1597 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1566
  have eq1600 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1597
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1597
    | exact resolve eq1597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq1664 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq16
    | exact resolve eq16 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1751 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1664
       have i₂ := eq1030 x y
       grind)
    | exact superpose eq1030 eq1664
    | (have j1 := eq1030 x y
       grind)
    | (have r₁ := eq1664
       have r₂ := eq1030 x y
       grind)
    | exact resolve eq1664 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1752 : x = (M.op y y) := by grind
  clear eq1751
  have eq1759 : (M.op x y) = (k x y) := by grind
  clear eq1752
  have eq1940 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1664
       have i₂ := eq1759
       grind)
    | exact superpose eq1759 eq1664
    | exact resolve eq1664 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq1759
  have eq1943 : False := by grind
  exact eq1943

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq303 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq2146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op (M.op (M.op X0 X1) X2) X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2416 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq303
    | (have j0 := eq303 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2417 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq2649 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2146 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq2146
    | exact resolve eq2146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2662 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X3) X4) X4) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2146 (M.op (M.op X0 X1) X0) X1 X2 X0 X4
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq2146
    | exact resolve eq2146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2717 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2649 X0 X1 (M.op X0 X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq2649
    | exact resolve eq2649 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2649 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq2649
    | exact resolve eq2649 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq3115 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X3) X3) X4) X4) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2662 (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2) (M.op X0 X0) X3 X4
       have i₂ := eq82 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq82 eq2662
    | exact resolve eq2662 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq35184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2416 x y
       grind)
    | exact superpose eq2416 eq16
    | (have j1 := eq2416 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2416 x y
       grind)
    | exact resolve eq16 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq35307 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq35184
  have eq35452 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq35307
  have eq35547 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35452
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq35452
    | exact resolve eq35452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35452
  have eq35558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq35547
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq35547 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35547
  have eq35565 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq35558
       have r₂ := eq16
       grind)
    | exact resolve eq35558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35558
  have eq35567 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35565
       grind)
    | exact superpose eq35565 eq16
    | exact resolve eq16 eq35565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35569 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq35565
       grind)
    | exact superpose eq35565 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq35565
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq35565
       grind)
    | exact resolve eq13 eq35565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35565
  have eq35635 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq35569
  have eq35649 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35635
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq35635
    | exact resolve eq35635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35635
  have eq35651 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq35649
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq35649 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35649
  have eq35652 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq35651
       have r₂ := eq35567
       grind)
    | exact resolve eq35651 eq35567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35567 eq35651
  have eq35995 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq35652
  have eq36126 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35995
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq35995
    | exact resolve eq35995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35995
  have eq36140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq36126
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq36126 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36126
  have eq36147 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36140
       have r₂ := eq16
       grind)
    | exact resolve eq36140 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36140
  have eq36151 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  have eq36170 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq36147
       grind)
    | exact superpose eq36147 eq9
    | exact resolve eq9 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2417 y
       have i₂ := eq36147
       grind)
    | exact superpose eq36147 eq2417
    | exact resolve eq2417 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36147
  have eq37780 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37665
       have r₂ := eq16
       grind)
    | exact resolve eq37665 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37665
  have eq40152 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37780
  have eq40257 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40152
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq40152
    | exact resolve eq40152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40152
  have eq40268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36151 eq40257
    | exact resolve eq40257 eq36151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40257
  have eq40275 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40268
       have r₂ := eq16
       grind)
    | exact resolve eq40268 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40268
  have eq40278 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40275
       grind)
    | exact superpose eq40275 eq16
    | exact resolve eq16 eq40275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40280 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq40275
       grind)
    | exact superpose eq40275 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq40275
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq40275
       grind)
    | exact resolve eq13 eq40275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40284 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq40275
       grind)
    | exact superpose eq40275 eq64
    | exact resolve eq64 eq40275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40354 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq40280
  have eq40370 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40354
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq40354
    | exact resolve eq40354 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40354
  have eq40373 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36151 eq40370
    | exact resolve eq40370 eq36151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40370
  have eq40375 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40373
       have r₂ := eq40278
       grind)
    | exact resolve eq40373 eq40278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40373
  have eq40377 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq40284
       grind)
    | exact superpose eq40284 eq70
    | exact resolve eq70 eq40284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq40513 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40377
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40377
    | exact resolve eq40377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40377
  have eq40527 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40284 eq40513
    | exact resolve eq40513 eq40284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40284 eq40513
  have eq40530 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40527
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40527
    | exact resolve eq40527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40527
  have eq40543 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq40530
       grind)
    | exact superpose eq40530 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq40530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40530
  have eq40544 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq40543
  have eq40566 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq40544
       grind)
    | exact superpose eq40544 eq64
    | exact resolve eq64 eq40544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq40544
  have eq40637 : x = (M.op x x) := by grind
  clear eq40566
  have eq40675 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36170 x
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq36170
    | exact resolve eq36170 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36170
  have eq40682 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2417 x
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq2417
    | (have j0 := eq2417 x
       grind)
    | exact resolve eq2417 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq40727 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) x) := by
    intro X0
    first
    | (have i₁ := eq2718 x x X0
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq2718
    | exact resolve eq2718 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40767 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq40682
  have eq40790 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq40727 X0
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq40727
    | exact resolve eq40727 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40727
  have eq40806 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40767
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq40767
    | exact resolve eq40767 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767
  have eq40807 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq40806
  have eq40809 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40675
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq40675
    | exact resolve eq40675 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40675
  have eq41224 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x X0) X1) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2717 (M.op x X0) x x
       have i₂ := eq40790 X0
       grind)
    | exact superpose eq40790 eq2717
    | exact resolve eq2717 eq40790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq40790
  have eq41293 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x X0) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq41224 X0 X1
       have i₂ := eq40637
       grind)
    | exact superpose eq40637 eq41224
    | exact resolve eq41224 eq40637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40637 eq41224
  have eq42044 : ∀ X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op x X1) X1) X2) X2) x) := by
    intro X1 X2
    first
    | (have i₁ := eq2662 x x x X1 X2
       have i₂ := eq41293 x x
       grind)
    | exact superpose eq41293 eq2662
    | exact resolve eq2662 eq41293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662 eq41293
  have eq42443 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40809 eq36151
    | exact resolve eq36151 eq40809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36151
  have eq42447 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40809 eq40278
    | exact resolve eq40278 eq40809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40278 eq40809
  have eq44500 : ∀ X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op x X1) X1) X2) X2) x) := by
    intro X1 X2
    first
    | (have j0 := eq42044 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42044
  have eq46107 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3115 x X0 X1 x x
       have i₂ := eq44500 x x
       grind)
    | exact superpose eq44500 eq3115
    | exact resolve eq3115 eq44500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115 eq44500
  have eq46590 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq40375
  have eq46746 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46590
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq46590
    | exact resolve eq46590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46590
  have eq46770 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40275 eq46746
    | exact resolve eq46746 eq40275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40275 eq46746
  have eq46782 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42443 eq46770
    | exact resolve eq46770 eq42443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42443 eq46770
  have eq46788 : x = (M.op x y) := by
    first
    | (have r₁ := eq46782
       have r₂ := eq42447
       grind)
    | exact resolve eq46782 eq42447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42447 eq46782
  have eq46789 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46788
       grind)
    | exact superpose eq46788 eq16
    | exact resolve eq16 eq46788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46796 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq46788
       grind)
    | exact superpose eq46788 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq46788
       grind)
    | exact resolve eq13 eq46788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46874 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq46796
  have eq46952 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq303 x y
       have i₂ := eq46874
       grind)
    | exact superpose eq46874 eq303
    | (have j0 := eq303 x y
       grind)
    | exact resolve eq303 eq46874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq46955 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq46952
  have eq46957 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq46955
       have r₂ := eq46789
       grind)
    | exact resolve eq46955 eq46789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46955
  have eq48981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq46957
  have eq49104 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq48981
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48981
    | exact resolve eq48981 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48981
  have eq49115 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq46874 eq49104
    | exact resolve eq49104 eq46874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46874 eq49104
  have eq49122 : x = (M.op y y) := by
    first
    | (have r₁ := eq49115
       have r₂ := eq46789
       grind)
    | exact resolve eq49115 eq46789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49115
  have eq49181 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq2718 y y X0
       have i₂ := eq49122
       grind)
    | exact superpose eq49122 eq2718
    | exact resolve eq2718 eq49122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq49122
  have eq49248 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq49181 X0
       have i₂ := eq46788
       grind)
    | exact superpose eq46788 eq49181
    | exact resolve eq49181 eq46788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49181
  have eq49457 : y = (M.op x y) := by
    first
    | (have i₁ := eq46107 x y
       have i₂ := eq49248 x
       grind)
    | exact superpose eq49248 eq46107
    | exact resolve eq46107 eq49248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46107 eq49248
  have eq49668 : x = y := by
    first
    | (have i₁ := eq49457
       have i₂ := eq46788
       grind)
    | exact superpose eq46788 eq49457
    | exact resolve eq49457 eq46788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46788 eq49457
  have eq49716 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq46789
       have i₂ := eq49668
       grind)
    | exact superpose eq49668 eq46789
    | exact resolve eq46789 eq49668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46789 eq49668
  have eq49718 : False := by grind
  exact eq49718

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq30
  have eq49 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq22 (σ X0) (σ X0)
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 (k X1 X0)
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq192 X0 X0
       grind)
    | exact resolve eq196 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq196
  have eq710 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq746 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq710
  have eq810 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq746
    | exact resolve eq746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq873 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq810 (τ X1) X0
       grind)
    | exact superpose eq810 eq18
    | (have j1 := eq810 (τ X1) X0
       grind)
    | exact resolve eq18 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1384 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq873 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq873
    | exact resolve eq873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1384 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1384
    | (have j0 := eq1384 X0 X1
       grind)
    | exact resolve eq1384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq722
       have i₂ := eq1438 y x
       grind)
    | exact superpose eq1438 eq722
    | (have j1 := eq1438 (σ y) (σ x)
       grind)
    | (have r₁ := eq722
       have r₂ := eq1438 y x
       grind)
    | exact resolve eq722 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1831 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1830
  have eq1900 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1831
  have eq2062 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq722
       have i₂ := eq1900
       grind)
    | exact superpose eq1900 eq722
    | exact resolve eq722 eq1900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq1900
  have eq2063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2062
  have eq2064 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2063
  have eq2075 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq49 x
       have i₂ := eq2064
       grind)
    | exact superpose eq2064 eq49
    | exact resolve eq49 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2093 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22 (σ x) (σ x)
       have i₂ := eq2064
       grind)
    | exact superpose eq2064 eq22
    | exact resolve eq22 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq2113 : y = (k y x) := by
    first
    | (have i₁ := eq2075
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2075
    | exact resolve eq2075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2125 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq810 y x
       have i₂ := eq2113
       grind)
    | exact superpose eq2113 eq810
    | (have j0 := eq810 y x
       grind)
    | exact resolve eq810 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq2113
  have eq2241 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2093
       grind)
    | exact superpose eq2093 eq16
    | exact resolve eq16 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq2529 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2241
       have i₂ := eq2125
       grind)
    | exact superpose eq2125 eq2241
    | exact resolve eq2241 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2554 : y = (M.op x x) := by grind
  clear eq2529
  have eq2568 : y = (M.op x y) := by
    first
    | (have i₁ := eq22 x x
       have i₂ := eq2554
       grind)
    | exact superpose eq2554 eq22
    | exact resolve eq22 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2554
  have eq2713 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2241
       have i₂ := eq2568
       grind)
    | exact superpose eq2568 eq2241
    | exact resolve eq2241 eq2568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241 eq2568
  have eq2738 : False := by grind
  exact eq2738

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_x_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
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
  have eq77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 (k X1 X0)
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq192 X0 X0
       grind)
    | exact resolve eq196 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq196
  have eq676 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq710 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq676
  have eq715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq824 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq715 (τ X1) X0
       grind)
    | exact superpose eq715 eq18
    | (have j1 := eq715 (τ X1) X0
       grind)
    | exact resolve eq18 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1066 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq824
    | exact resolve eq824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq1118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1066
    | (have j0 := eq1066 X0 X1
       grind)
    | exact resolve eq1066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq688
       have i₂ := eq1118 y x
       grind)
    | exact superpose eq1118 eq688
    | (have j1 := eq1118 (σ y) (σ x)
       grind)
    | (have r₁ := eq688
       have r₂ := eq1118 y x
       grind)
    | exact resolve eq688 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1778 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1777
  have eq1785 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq1791 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x x
       have i₂ := eq1778
       grind)
    | exact superpose eq1778 eq35
    | exact resolve eq35 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1869 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq688
       have i₂ := eq1785
       grind)
    | exact superpose eq1785 eq688
    | exact resolve eq688 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq1785
  have eq1874 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1869
  have eq2006 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1874
       have i₂ := eq1791
       grind)
    | exact superpose eq1791 eq1874
    | exact resolve eq1874 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791 eq1874
  have eq2007 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2006
  have eq2008 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2007
  have eq2013 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq2008
       grind)
    | exact superpose eq2008 eq43
    | exact resolve eq43 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2029 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 (σ x) (σ x)
       have i₂ := eq2008
       grind)
    | exact superpose eq2008 eq35
    | exact resolve eq35 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2048 : y = (k y x) := by
    first
    | (have i₁ := eq2013
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2013
    | exact resolve eq2013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2062 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq715 y x
       have i₂ := eq2048
       grind)
    | exact superpose eq2048 eq715
    | (have j0 := eq715 y x
       grind)
    | exact resolve eq715 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq2048
  have eq2175 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2029
       grind)
    | exact superpose eq2029 eq16
    | exact resolve eq16 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2339 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2175
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq2175
    | exact resolve eq2175 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2365 : y = (M.op x x) := by grind
  clear eq2339
  have eq2503 : y = (M.op x y) := by
    first
    | (have i₁ := eq35 x x
       have i₂ := eq2365
       grind)
    | exact superpose eq2365 eq35
    | exact resolve eq35 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2365
  have eq2522 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2175
       have i₂ := eq2503
       grind)
    | exact superpose eq2503 eq2175
    | exact resolve eq2175 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175 eq2503
  have eq2548 : False := by grind
  exact eq2548

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq70 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq19
    | exact resolve eq19 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq23
    | exact resolve eq23 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq70 (τ X0)
       grind)
    | exact superpose eq70 eq19
    | exact resolve eq19 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq383 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq386 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
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
  have eq407 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2650 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 x
       have i₂ := eq407 (τ x) x
       grind)
    | exact superpose eq407 eq70
    | (have j1 := eq407 (τ X0) X0
       grind)
    | exact resolve eq70 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq407
  have eq2708 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2711 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2708 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2708
    | (have j0 := eq2708 X0
       grind)
    | exact resolve eq2708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2708
  have eq2736 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2711 (σ X0)
       grind)
    | exact superpose eq2711 eq23
    | (have j1 := eq2711 (σ X0)
       grind)
    | exact resolve eq23 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2784 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2736 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2736
    | (have j0 := eq2736 X0
       grind)
    | exact resolve eq2736 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2824 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2784 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2784
    | (have j0 := eq2784 X0
       grind)
    | exact resolve eq2784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2860 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2824 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2824
    | (have j0 := eq2824 X0
       grind)
    | exact resolve eq2824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2933 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2860 (σ X0)
       grind)
    | exact superpose eq2860 eq23
    | (have j1 := eq2860 (σ X0)
       grind)
    | exact resolve eq23 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2981 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2933 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2933
    | (have j0 := eq2933 X0
       grind)
    | exact resolve eq2933 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2933
  have eq3021 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2981 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2981
    | (have j0 := eq2981 X0
       grind)
    | exact resolve eq2981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq3497 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq384
    | (have j0 := eq384 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq384 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3498 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq384 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq384
    | (have j0 := eq384 (M.op X0 X0) X0
       grind)
    | exact resolve eq384 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3534 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq384 X1 X0
       grind)
    | exact superpose eq384 eq15
    | (have j1 := eq384 X1 X0
       grind)
    | exact resolve eq15 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq16330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 (σ X0)
       have i₂ := eq3534 X0 X0 X0
       grind)
    | exact superpose eq3534 eq69
    | (have j1 := eq3534 X0 X0 x
       grind)
    | exact resolve eq69 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3534
  have eq16347 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16330 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16330
  have eq16363 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq3021 eq16347
    | (have j0 := eq16347 X0
       have j1 := eq3021 X0
       grind)
    | exact resolve eq16347 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021 eq16347
  have eq16389 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16363 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq16363
    | (have j0 := eq16363 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq16363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16363
  have eq16477 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16389
  have eq18351 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq16477 X0
       grind)
    | exact superpose eq16477 eq64
    | (have j1 := eq16477 X0
       grind)
    | exact resolve eq64 eq16477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16477
  have eq18462 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq3498 X0
       grind)
    | exact superpose eq3498 eq383
    | (have j1 := eq3498 X0
       grind)
    | (have r₁ := eq383 (σ X0) (σ (M.op X0 X0))
       have r₂ := eq3498 X0
       grind)
    | exact resolve eq383 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq3498
  have eq18504 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq18462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462
  have eq18514 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18504 X0
       have j1 := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq18504 X0
       have r₂ := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq18504 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18504
  have eq18527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18514 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq18514
    | (have j0 := eq18514 X0
       grind)
    | exact resolve eq18514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18514
  have eq18533 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18527 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq18527
    | (have j0 := eq18527 X0
       grind)
    | exact resolve eq18527 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527
  have eq18534 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq18533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18533
  have eq23685 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3497 x y
       grind)
    | exact superpose eq3497 eq16
    | (have j1 := eq3497 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3497 x y
       grind)
    | exact resolve eq16 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq23818 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq23685
  have eq88893 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71 x
       have i₂ := eq23818
       grind)
    | exact superpose eq23818 eq71
    | exact resolve eq71 eq23818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ x)
       have i₂ := eq23818
       grind)
    | exact superpose eq23818 eq64
    | exact resolve eq64 eq23818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23818
  have eq89081 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88893
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq88893
    | exact resolve eq88893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88893
  have eq89110 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq89081
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq89081 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89081
  have eq89132 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq89110
       grind)
    | exact superpose eq89110 eq64
    | exact resolve eq64 eq89110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95503 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq386 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq386 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq386 X0 X0
       grind)
    | exact resolve eq13 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95597 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq95600 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95503 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95503
  have eq95658 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95600 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq95600 X0 X0
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq95600 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq95600 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95600
  have eq95717 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95658 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq95658
    | (have j0 := eq95658 X0 X1
       grind)
    | exact resolve eq95658 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq95658
  have eq95808 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95597 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq95597
    | (have j0 := eq95597 (σ X1) (σ X0)
       grind)
    | exact resolve eq95597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95597
  have eq95902 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95808 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq95808
    | (have j0 := eq95808 X0 X1
       grind)
    | exact resolve eq95808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95808
  have eq95944 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95902 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq95902
    | (have j0 := eq95902 X0 X1
       grind)
    | exact resolve eq95902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95902
  have eq95984 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95944 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95944
    | (have j0 := eq95944 X0 X1
       grind)
    | exact resolve eq95944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95944
  have eq96022 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95984 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95984
    | (have j0 := eq95984 X0 X1
       grind)
    | exact resolve eq95984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95984
  have eq96050 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96022 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96022
    | (have j0 := eq96022 X0 X1
       grind)
    | exact resolve eq96022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96022
  have eq96069 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96050 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96050
    | (have j0 := eq96050 X0 X1
       grind)
    | exact resolve eq96050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96050
  have eq96119 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96069 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq96069
    | (have j0 := eq96069 (σ X0) (σ X1)
       grind)
    | exact resolve eq96069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96069
  have eq96447 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95717 (M.op x x) x
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq95717
    | (have j0 := eq95717 (M.op X0 X0) X0
       grind)
    | exact resolve eq95717 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq96458 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq95717 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq95717
    | (have j0 := eq95717 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq95717 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96473 : ∀ X0 : G, (τ X0) ≠ (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq95717 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq95717
    | (have j0 := eq95717 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq95717 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq95717
  have eq96522 : ∀ X0 : G, (τ X0) ≠ (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq96473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96473
  have eq96529 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq96447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96447
  have eq96562 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96458 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq96458
    | (have j0 := eq96458 X0 X1
       grind)
    | exact resolve eq96458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96458
  have eq96602 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96562 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq96562
    | (have j0 := eq96562 X0 X1
       grind)
    | exact resolve eq96562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96562
  have eq96638 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96602 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96602
    | (have j0 := eq96602 X0 X1
       grind)
    | exact resolve eq96602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96602
  have eq96669 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96638 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq96638
    | (have j0 := eq96638 X0 X1
       grind)
    | exact resolve eq96638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96638
  have eq96691 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96669 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96669
    | (have j0 := eq96669 X0 X1
       grind)
    | exact resolve eq96669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96669
  have eq96713 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96691 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96691
    | (have j0 := eq96691 X0 X1
       grind)
    | exact resolve eq96691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96691
  have eq96819 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ≠ X0 ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq96713 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq96713
    | (have j0 := eq96713 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0
       grind)
    | exact resolve eq96713 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq96713
  have eq96872 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ≠ X0 ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) := by
    intro X0
    first
    | (have j0 := eq96819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96819
  have eq97140 : (τ (τ (σ x))) ≠ (τ x) ∨ (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96522 x
       have i₂ := eq89132
       grind)
    | exact superpose eq89132 eq96522
    | exact resolve eq96522 eq89132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89132 eq96522
  have eq97156 : (τ x) ≠ (τ x) ∨ (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97140
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97140
    | exact resolve eq97140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97140
  have eq97157 : (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq97156
  have eq97172 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97157
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97157
    | exact resolve eq97157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97157
  have eq97831 : ∀ X0 : G, (σ X0) ≠ (σ (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq96872 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96872
    | exact resolve eq96872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96872
  have eq99449 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88951
       grind)
    | exact superpose eq88951 eq16
    | exact resolve eq16 eq88951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88951
  have eq99597 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq89110 eq99449
    | exact resolve eq99449 eq89110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89110 eq99449
  have eq99598 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq99597
  have eq99641 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99598
       grind)
    | exact superpose eq99598 eq16
    | exact resolve eq16 eq99598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99656 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq99598
       grind)
    | exact superpose eq99598 eq64
    | exact resolve eq64 eq99598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99823 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96529 (σ x)
       have i₂ := eq99656
       grind)
    | exact superpose eq99656 eq96529
    | exact resolve eq96529 eq99656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99920 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq99823
  have eq99961 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99920
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99920
    | exact resolve eq99920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99920
  have eq100008 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18351 x
       have i₂ := eq99961
       grind)
    | exact superpose eq99961 eq18351
    | (have j0 := eq18351 x
       grind)
    | exact resolve eq18351 eq99961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18351
  have eq100035 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq99961
       grind)
    | exact superpose eq99961 eq64
    | exact resolve eq64 eq99961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100123 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq99961
  have eq100148 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq99656 eq100008
    | exact resolve eq100008 eq99656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99656 eq100008
  have eq100149 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq100148
  have eq100308 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq100035 eq97172
    | exact resolve eq97172 eq100035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97172 eq100035
  have eq103688 : (σ x) ≠ (σ (σ (τ x))) ∨ (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq97831 x
       have i₂ := eq100308
       grind)
    | exact superpose eq100308 eq97831
    | exact resolve eq97831 eq100308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97831 eq100308
  have eq103883 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103688
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq103688
    | exact resolve eq103688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103688
  have eq103884 : (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq103883
  have eq103900 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103884
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq103884
    | exact resolve eq103884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103884
  have eq111606 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100149
       grind)
    | exact superpose eq100149 eq16
    | exact resolve eq16 eq100149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100149
  have eq111752 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq103900 eq111606
    | exact resolve eq111606 eq103900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103900 eq111606
  have eq111753 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq111752
  have eq111818 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96529 (σ x)
       have i₂ := eq111753
       grind)
    | exact superpose eq111753 eq96529
    | exact resolve eq96529 eq111753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96529 eq111753
  have eq111919 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq111818
  have eq111966 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111919
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111919
    | exact resolve eq111919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111919
  have eq111988 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq111966
       have r₂ := eq100123
       grind)
    | exact resolve eq111966 eq100123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100123 eq111966
  have eq112000 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq111988 eq99598
    | exact resolve eq99598 eq111988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99598
  have eq112001 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq111988 eq99641
    | exact resolve eq99641 eq111988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99641
  have eq112019 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq111988
       grind)
    | exact superpose eq111988 eq64
    | exact resolve eq64 eq111988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq111988
  have eq112114 : x = (M.op x x) := by grind
  clear eq112019
  have eq112174 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18534 x
       have i₂ := eq112114
       grind)
    | exact superpose eq112114 eq18534
    | exact resolve eq18534 eq112114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18534
  have eq112294 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq112174
  have eq125111 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq112000
       grind)
    | exact superpose eq112000 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq112000
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq112000
       grind)
    | exact resolve eq13 eq112000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112000
  have eq125209 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq125111
  have eq125290 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq125209
       have i₂ := eq112294
       grind)
    | exact superpose eq112294 eq125209
    | exact resolve eq125209 eq112294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125209
  have eq125331 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq125290
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq125290
    | exact resolve eq125290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125290
  have eq125340 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq125331
       have i₂ := eq112294
       grind)
    | exact superpose eq112294 eq125331
    | exact resolve eq125331 eq112294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125331
  have eq156509 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq125340
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq125340
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq125340 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125340
  have eq156627 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq156509
  have eq156706 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq156627
       have r₂ := eq112001
       grind)
    | exact resolve eq156627 eq112001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112001 eq156627
  have eq156712 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq156706
       have i₂ := eq112114
       grind)
    | exact superpose eq112114 eq156706
    | exact resolve eq156706 eq112114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156706
  have eq156713 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq156712
  have eq156756 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq156713
       grind)
    | exact superpose eq156713 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq156713
       grind)
    | exact resolve eq13 eq156713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156859 : y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq156756
  have eq156915 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156859
       have i₂ := eq112114
       grind)
    | exact superpose eq112114 eq156859
    | exact resolve eq156859 eq112114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156859
  have eq156916 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq156915
  have eq156941 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq156916
       have i₂ := eq112114
       grind)
    | exact superpose eq112114 eq156916
    | exact resolve eq156916 eq112114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156916
  have eq156955 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96119 y x
       have i₂ := eq156941
       grind)
    | exact superpose eq156941 eq96119
    | (have j0 := eq96119 y x
       grind)
    | exact resolve eq96119 eq156941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96119 eq156941
  have eq156960 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq156955
  have eq156967 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq156960
       have i₂ := eq112294
       grind)
    | exact superpose eq112294 eq156960
    | exact resolve eq156960 eq112294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156960
  have eq156968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq156967
  have eq156973 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq156968
       grind)
    | exact superpose eq156968 eq16
    | exact resolve eq16 eq156968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156968
  have eq157181 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq156713 eq156973
    | exact resolve eq156973 eq156713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156713 eq156973
  have eq157182 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq157181
  have eq157219 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq157182
       grind)
    | exact superpose eq157182 eq10
    | exact resolve eq10 eq157182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157182
  have eq157405 : x = y ∨ x = y := by
    first
    | (have i₁ := eq157219
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq157219
    | exact resolve eq157219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157219
  have eq157406 : x = y := by grind
  clear eq157405
  have eq157421 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157406
       grind)
    | exact superpose eq157406 eq16
    | exact resolve eq16 eq157406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157406
  have eq157422 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq157421
       have i₂ := eq112114
       grind)
    | exact superpose eq112114 eq157421
    | exact resolve eq157421 eq112114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112114 eq157421
  have eq157423 : False := by grind
  exact eq157423

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq387 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1439 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq385
    | (have j0 := eq385 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1469 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq385 X1 X0
       grind)
    | exact superpose eq385 eq15
    | (have j1 := eq385 X1 X0
       grind)
    | exact resolve eq15 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2810 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x
       have i₂ := eq408 (τ x) x
       grind)
    | exact superpose eq408 eq25
    | (have j1 := eq408 (τ X0) X0
       grind)
    | exact resolve eq25 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq408
  have eq2868 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq2871 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2868 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2868
    | (have j0 := eq2868 X0
       grind)
    | exact resolve eq2868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2897 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2871 (σ X0)
       grind)
    | exact superpose eq2871 eq23
    | (have j1 := eq2871 (σ X0)
       grind)
    | exact resolve eq23 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq2945 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2897 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2897
    | (have j0 := eq2897 X0
       grind)
    | exact resolve eq2897 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897
  have eq2985 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2945 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2945
    | (have j0 := eq2945 X0
       grind)
    | exact resolve eq2945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq3021 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2985 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2985
    | (have j0 := eq2985 X0
       grind)
    | exact resolve eq2985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq3095 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq3021 (σ X0)
       grind)
    | exact superpose eq3021 eq23
    | (have j1 := eq3021 (σ X0)
       grind)
    | exact resolve eq23 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3143 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3095 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq3095
    | (have j0 := eq3095 X0
       grind)
    | exact resolve eq3095 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3095
  have eq3183 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3143 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3143
    | (have j0 := eq3143 X0
       grind)
    | exact resolve eq3143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq16329 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq1469
  have eq16346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq16329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16329
  have eq16362 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq3183 eq16346
    | (have j0 := eq16346 X0
       have j1 := eq3183 X0
       grind)
    | exact resolve eq16346 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183 eq16346
  have eq16388 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16362 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq16362
    | (have j0 := eq16362 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq16362 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16406 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq16362 (τ X0)
       grind)
    | exact superpose eq16362 eq19
    | (have j1 := eq16362 (τ X0)
       grind)
    | exact resolve eq19 eq16362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16476 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16388
  have eq16481 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16406 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16406
    | (have j0 := eq16406 X0
       grind)
    | exact resolve eq16406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16406
  have eq16502 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16481 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16481
    | (have j0 := eq16481 X0
       grind)
    | exact resolve eq16481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16481
  have eq16532 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16502 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq16502
    | (have j0 := eq16502 (τ X0)
       grind)
    | exact resolve eq16502 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq16502
  have eq16842 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq16532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16532
  have eq16878 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16842 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq16842
    | (have j0 := eq16842 (σ X0)
       grind)
    | exact resolve eq16842 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16842
  have eq16896 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16878 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16878
    | (have j0 := eq16878 X0
       grind)
    | exact resolve eq16878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16878
  have eq16919 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16896 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16896
    | (have j0 := eq16896 X0
       grind)
    | exact resolve eq16896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16896
  have eq18243 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq16476 X0
       grind)
    | exact superpose eq16476 eq66
    | (have j1 := eq16476 X0
       grind)
    | exact resolve eq66 eq16476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq29888 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1439 x y
       grind)
    | exact superpose eq1439 eq16
    | (have j1 := eq1439 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1439 x y
       grind)
    | exact resolve eq16 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq30029 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29888
  have eq91155 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq91191 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ x)
       have i₂ := eq30029
       grind)
    | exact superpose eq30029 eq66
    | exact resolve eq66 eq30029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30029
  have eq91310 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91155
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq91155
    | exact resolve eq91155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91155
  have eq91347 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq91310
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq91310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91310
  have eq96391 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq96585 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq96391
  have eq97227 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91191
       grind)
    | exact superpose eq91191 eq16
    | exact resolve eq16 eq91191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91191
  have eq97376 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq97227
       have r₂ := eq91347
       grind)
    | exact resolve eq97227 eq91347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91347 eq97227
  have eq97415 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97376
       grind)
    | exact superpose eq97376 eq16
    | exact resolve eq16 eq97376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97426 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq97376
       grind)
    | exact superpose eq97376 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq97376
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq97376
       grind)
    | exact resolve eq13 eq97376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97430 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ y)
       have i₂ := eq97376
       grind)
    | exact superpose eq97376 eq66
    | exact resolve eq66 eq97376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97376
  have eq97520 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq97426
  have eq97539 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97520
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq97520
    | exact resolve eq97520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97520
  have eq97545 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq97539
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq97539 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97539
  have eq97549 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq97545
       have r₂ := eq97415
       grind)
    | exact resolve eq97545 eq97415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97415 eq97545
  have eq97557 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq97430
       grind)
    | exact superpose eq97430 eq36
    | exact resolve eq36 eq97430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97733 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq97557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97557
    | exact resolve eq97557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97557
  have eq97789 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq97733
       grind)
    | exact superpose eq97733 eq66
    | exact resolve eq66 eq97733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97733
  have eq97982 : x ≠ y ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  have eq98006 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq97430 eq97549
    | exact resolve eq97549 eq97430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97549
  have eq98047 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq98006
       grind)
    | exact superpose eq98006 eq66
    | exact resolve eq66 eq98006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98239 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq98047
  have eq204541 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96585 (σ x)
       have i₂ := eq97430
       grind)
    | exact superpose eq97430 eq96585
    | exact resolve eq96585 eq97430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204566 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq204541
  have eq204567 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq204566
  have eq204600 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq204567
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq204567
    | exact resolve eq204567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204567
  have eq204668 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18243 x
       have i₂ := eq204600
       grind)
    | exact superpose eq204600 eq18243
    | (have j0 := eq18243 x
       grind)
    | exact resolve eq18243 eq204600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18243 eq204600
  have eq204880 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97430 eq204668
    | exact resolve eq204668 eq97430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97430 eq204668
  have eq204881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq204880
  have eq209791 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204881
       grind)
    | exact superpose eq204881 eq16
    | exact resolve eq16 eq204881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204881
  have eq210030 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq209791
       have i₂ := eq97789
       grind)
    | exact superpose eq97789 eq209791
    | exact resolve eq209791 eq97789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97789 eq209791
  have eq210031 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq210030
  have eq210032 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq210031
  have eq210037 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq210032
       have r₂ := eq97982
       grind)
    | exact resolve eq210032 eq97982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97982 eq210032
  have eq210093 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq96585 (σ x)
       have i₂ := eq210037
       grind)
    | exact superpose eq210037 eq96585
    | exact resolve eq96585 eq210037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96585 eq210037
  have eq210235 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq210093
  have eq210236 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq210235
  have eq210308 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq210236
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq210236
    | exact resolve eq210236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210236
  have eq210340 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq16919 x
       grind)
    | (have r₁ := eq210308
       have r₂ := eq16919 x
       grind)
    | exact resolve eq210308 eq16919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16919 eq210308
  have eq210440 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq210340 eq98006
    | exact resolve eq98006 eq210340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98006
  have eq210452 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq210340
       grind)
    | exact superpose eq210340 eq66
    | exact resolve eq66 eq210340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq210340
  have eq210592 : x = (M.op x x) := by grind
  clear eq210452
  have eq210626 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq210440
       have r₂ := eq98239
       grind)
    | exact resolve eq210440 eq98239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98239 eq210440
  have eq210668 : x = (k x x) := by grind
  have eq210960 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16362 x
       have i₂ := eq210668
       grind)
    | exact superpose eq210668 eq16362
    | (have j0 := eq16362 x
       grind)
    | exact resolve eq16362 eq210668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16362 eq210668
  have eq211000 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq210960
  have eq212497 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq211000
  have eq215288 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq210626
       grind)
    | exact superpose eq210626 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq210626
       grind)
    | exact resolve eq13 eq210626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215433 : y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq215288
  have eq215555 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq215433
       have i₂ := eq210592
       grind)
    | exact superpose eq210592 eq215433
    | exact resolve eq215433 eq210592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215433
  have eq222941 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq385 y x
       have i₂ := eq215555
       grind)
    | exact superpose eq215555 eq385
    | (have j0 := eq385 y x
       grind)
    | exact resolve eq385 eq215555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq215555
  have eq222944 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq222941
  have eq222949 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222944
       have i₂ := eq212497
       grind)
    | exact superpose eq212497 eq222944
    | exact resolve eq222944 eq212497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222944
  have eq222950 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq222949
  have eq234599 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq222950
       grind)
    | exact superpose eq222950 eq16
    | exact resolve eq16 eq222950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222950
  have eq234890 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq210626 eq234599
    | exact resolve eq234599 eq210626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210626 eq234599
  have eq234891 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq234890
  have eq234980 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq234891
       grind)
    | exact superpose eq234891 eq10
    | exact resolve eq10 eq234891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234891
  have eq235185 : x = y ∨ x = y := by
    first
    | (have i₁ := eq234980
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq234980
    | exact resolve eq234980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234980
  have eq235186 : x = y := by grind
  clear eq235185
  have eq235198 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235186
       grind)
    | exact superpose eq235186 eq16
    | exact resolve eq16 eq235186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235186
  have eq235199 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq235198
       have i₂ := eq210592
       grind)
    | exact superpose eq210592 eq235198
    | exact resolve eq235198 eq210592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210592 eq235198
  have eq235200 : False := by grind
  exact eq235200

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_x_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq19
    | exact resolve eq19 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq384 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq387 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2649 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x
       have i₂ := eq408 (τ x) x
       grind)
    | exact superpose eq408 eq25
    | (have j1 := eq408 (τ X0) X0
       grind)
    | exact resolve eq25 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq408
  have eq2707 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649
  have eq2710 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2707 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2707
    | (have j0 := eq2707 X0
       grind)
    | exact resolve eq2707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2735 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2710 (σ X0)
       grind)
    | exact superpose eq2710 eq23
    | (have j1 := eq2710 (σ X0)
       grind)
    | exact resolve eq23 eq2710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2783 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2735 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2735
    | (have j0 := eq2735 X0
       grind)
    | exact resolve eq2735 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2823 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2783 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2783
    | (have j0 := eq2783 X0
       grind)
    | exact resolve eq2783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2859 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2823 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2823
    | (have j0 := eq2823 X0
       grind)
    | exact resolve eq2823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq2932 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (k (σ X0) (σ X0)) X0
       have i₂ := eq2859 (σ X0)
       grind)
    | exact superpose eq2859 eq23
    | (have j1 := eq2859 (σ X0)
       grind)
    | exact resolve eq23 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2980 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2932 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq2932
    | (have j0 := eq2932 X0
       grind)
    | exact resolve eq2932 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2932
  have eq3020 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2980 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2980
    | (have j0 := eq2980 X0
       grind)
    | exact resolve eq2980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq13405 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq385
    | (have j0 := eq385 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13410 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq13457 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq385 X1 X0
       grind)
    | exact superpose eq385 eq15
    | (have j1 := eq385 X1 X0
       grind)
    | exact resolve eq15 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq23375 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq13457
  have eq23393 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq23375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23375
  have eq23410 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq3020 eq23393
    | (have j0 := eq23393 X0
       have j1 := eq3020 X0
       grind)
    | exact resolve eq23393 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq23393
  have eq23445 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23410 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq23410
    | (have j0 := eq23410 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq23410 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23410
  have eq23542 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23445
  have eq25569 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq23542 X0
       grind)
    | exact superpose eq23542 eq66
    | (have j1 := eq23542 X0
       grind)
    | exact resolve eq66 eq23542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23542
  have eq28248 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq384 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq13410 X0
       grind)
    | exact superpose eq13410 eq384
    | (have j1 := eq13410 X0
       grind)
    | (have r₁ := eq384 (σ X0) (σ (M.op X0 X0))
       have r₂ := eq13410 X0
       grind)
    | exact resolve eq384 eq13410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq13410
  have eq28301 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq28248 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28248
  have eq28313 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq28301 X0
       have j1 := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq28301 X0
       have r₂ := eq13 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact resolve eq28301 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28301
  have eq28330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28313 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq28313
    | (have j0 := eq28313 X0
       grind)
    | exact resolve eq28313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28313
  have eq28336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq28330
  have eq28337 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq28336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28336
  have eq35561 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13405 x y
       grind)
    | exact superpose eq13405 eq16
    | (have j1 := eq13405 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq13405 x y
       grind)
    | exact resolve eq16 eq13405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13405
  have eq35708 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq35561
  have eq84735 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq35708
       grind)
    | exact superpose eq35708 eq36
    | exact resolve eq36 eq35708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84787 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ x)
       have i₂ := eq35708
       grind)
    | exact superpose eq35708 eq66
    | exact resolve eq66 eq35708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35708
  have eq84917 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84735
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq84735
    | exact resolve eq84735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84735
  have eq84946 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq84917
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq84917 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84917
  have eq84963 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ y)
       have i₂ := eq84946
       grind)
    | exact superpose eq84946 eq66
    | exact resolve eq66 eq84946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98281 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq387 X0 X1
       grind)
    | exact superpose eq387 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq387 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq387 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq387 X0 X0
       grind)
    | exact resolve eq13 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98379 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq98382 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq98281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98281
  have eq98440 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98382 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq98382 X0 X0
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq98382 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq98382 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98382
  have eq98499 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98440 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq98440
    | (have j0 := eq98440 X0 X1
       grind)
    | exact resolve eq98440 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq98440
  have eq98590 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98379 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq98379
    | (have j0 := eq98379 (σ X1) (σ X0)
       grind)
    | exact resolve eq98379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98379
  have eq98688 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98590 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq98590
    | (have j0 := eq98590 X0 X1
       grind)
    | exact resolve eq98590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98590
  have eq98732 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98688 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq98688
    | (have j0 := eq98688 X0 X1
       grind)
    | exact resolve eq98688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98688
  have eq98774 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98732 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98732
    | (have j0 := eq98732 X0 X1
       grind)
    | exact resolve eq98732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98732
  have eq98814 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98774 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98774
    | (have j0 := eq98774 X0 X1
       grind)
    | exact resolve eq98774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98774
  have eq98843 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98814 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98814
    | (have j0 := eq98814 X0 X1
       grind)
    | exact resolve eq98814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98814
  have eq98863 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98843 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98843
    | (have j0 := eq98843 X0 X1
       grind)
    | exact resolve eq98843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98843
  have eq98913 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98863 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq98863
    | (have j0 := eq98863 (σ X0) (σ X1)
       grind)
    | exact resolve eq98863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98863
  have eq99241 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    grind
  have eq99252 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq98499 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq98499
    | (have j0 := eq98499 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq98499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99267 : ∀ X0 : G, (τ X0) ≠ (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq98499 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq98499
    | (have j0 := eq98499 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq98499 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq98499
  have eq99318 : ∀ X0 : G, (τ X0) ≠ (τ (τ (M.op (σ X0) (σ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq99267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99267
  have eq99325 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq99241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99241
  have eq99360 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99252 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq99252
    | (have j0 := eq99252 X0 X1
       grind)
    | exact resolve eq99252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99252
  have eq99402 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99360 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq99360
    | (have j0 := eq99360 X0 X1
       grind)
    | exact resolve eq99360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99360
  have eq99439 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99402 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99402
    | (have j0 := eq99402 X0 X1
       grind)
    | exact resolve eq99402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99402
  have eq99471 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99439 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq99439
    | (have j0 := eq99439 X0 X1
       grind)
    | exact resolve eq99439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99439
  have eq99494 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99471 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99471
    | (have j0 := eq99471 X0 X1
       grind)
    | exact resolve eq99471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99471
  have eq99517 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99494 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99494
    | (have j0 := eq99494 X0 X1
       grind)
    | exact resolve eq99494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99494
  have eq99623 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ≠ X0 ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq99517 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq99517
    | (have j0 := eq99517 (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0
       grind)
    | exact resolve eq99517 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq99517
  have eq99676 : ∀ X0 : G, (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) ≠ X0 ∨ (M.op X0 X0) = (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) := by
    intro X0
    first
    | (have j0 := eq99623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99623
  have eq99950 : (τ (τ (σ x))) ≠ (τ x) ∨ (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99318 x
       have i₂ := eq84963
       grind)
    | exact superpose eq84963 eq99318
    | exact resolve eq99318 eq84963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84963 eq99318
  have eq99966 : (τ x) ≠ (τ x) ∨ (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99950
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99950
    | exact resolve eq99950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99950
  have eq99967 : (τ (τ (σ x))) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq99966
  have eq99982 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99967
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99967
    | exact resolve eq99967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99967
  have eq100655 : ∀ X0 : G, (σ X0) ≠ (σ (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq99676 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99676
    | exact resolve eq99676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99676
  have eq102317 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84787
       grind)
    | exact superpose eq84787 eq16
    | exact resolve eq16 eq84787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84787
  have eq102469 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq84946 eq102317
    | exact resolve eq102317 eq84946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84946 eq102317
  have eq102470 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq102469
  have eq102513 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102470
       grind)
    | exact superpose eq102470 eq16
    | exact resolve eq16 eq102470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102528 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 (σ x) (σ y)
       have i₂ := eq102470
       grind)
    | exact superpose eq102470 eq66
    | exact resolve eq66 eq102470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102700 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99325 (σ x)
       have i₂ := eq102528
       grind)
    | exact superpose eq102528 eq99325
    | exact resolve eq99325 eq102528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102801 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq102700
  have eq102844 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102801
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102801
    | exact resolve eq102801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102801
  have eq102897 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25569 x
       have i₂ := eq102844
       grind)
    | exact superpose eq102844 eq25569
    | (have j0 := eq25569 x
       grind)
    | exact resolve eq25569 eq102844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25569
  have eq102918 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq102844
       grind)
    | exact superpose eq102844 eq66
    | exact resolve eq66 eq102844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103010 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq102844
  have eq103035 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102528 eq102897
    | exact resolve eq102897 eq102528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102528 eq102897
  have eq103036 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq103035
  have eq103199 : (τ x) = (M.op (τ x) (τ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102918 eq99982
    | exact resolve eq99982 eq102918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99982 eq102918
  have eq105882 : (σ x) ≠ (σ (σ (τ x))) ∨ (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq100655 x
       have i₂ := eq103199
       grind)
    | exact superpose eq103199 eq100655
    | exact resolve eq100655 eq103199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100655 eq103199
  have eq106080 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq105882
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq105882
    | exact resolve eq105882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105882
  have eq106081 : (M.op (σ x) (σ x)) = (σ (σ (τ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq106080
  have eq106097 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq106081
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq106081
    | exact resolve eq106081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106081
  have eq112951 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103036
       grind)
    | exact superpose eq103036 eq16
    | exact resolve eq16 eq103036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103036
  have eq113097 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq106097 eq112951
    | exact resolve eq112951 eq106097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106097 eq112951
  have eq113098 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq113097
  have eq113163 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99325 (σ x)
       have i₂ := eq113098
       grind)
    | exact superpose eq113098 eq99325
    | exact resolve eq99325 eq113098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99325 eq113098
  have eq113264 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq113163
  have eq113311 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113264
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113264
    | exact resolve eq113264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113264
  have eq113333 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq113311
       have r₂ := eq103010
       grind)
    | exact resolve eq113311 eq103010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103010 eq113311
  have eq113345 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq113333 eq102470
    | exact resolve eq102470 eq113333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102470
  have eq113346 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq113333 eq102513
    | exact resolve eq102513 eq113333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102513
  have eq113364 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq113333
       grind)
    | exact superpose eq113333 eq66
    | exact resolve eq66 eq113333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq113333
  have eq113459 : x = (M.op x x) := by grind
  clear eq113364
  have eq113525 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq28337 x
       have i₂ := eq113459
       grind)
    | exact superpose eq113459 eq28337
    | exact resolve eq28337 eq113459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28337
  have eq113639 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq113525
  have eq126436 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq113345
       grind)
    | exact superpose eq113345 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq113345
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq113345
       grind)
    | exact resolve eq13 eq113345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113345
  have eq126536 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq126436
  have eq126619 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126536
       have i₂ := eq113639
       grind)
    | exact superpose eq113639 eq126536
    | exact resolve eq126536 eq113639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126536
  have eq126661 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126619
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq126619
    | exact resolve eq126619 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126619
  have eq126670 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq126661
       have i₂ := eq113639
       grind)
    | exact superpose eq113639 eq126661
    | exact resolve eq126661 eq113639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126661
  have eq161527 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq126670
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq126670
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq126670 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126670
  have eq161649 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq161527
  have eq161728 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq161649
       have r₂ := eq113346
       grind)
    | exact resolve eq161649 eq113346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113346 eq161649
  have eq161734 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq161728
       have i₂ := eq113459
       grind)
    | exact superpose eq113459 eq161728
    | exact resolve eq161728 eq113459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161728
  have eq161735 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq161734
  have eq161778 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq161735
       grind)
    | exact superpose eq161735 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq161735
       grind)
    | exact resolve eq13 eq161735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161885 : y = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq161778
  have eq161945 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq161885
       have i₂ := eq113459
       grind)
    | exact superpose eq113459 eq161885
    | exact resolve eq161885 eq113459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161885
  have eq161946 : x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq161945
  have eq161971 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq161946
       have i₂ := eq113459
       grind)
    | exact superpose eq113459 eq161946
    | exact resolve eq161946 eq113459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161946
  have eq161985 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98913 y x
       have i₂ := eq161971
       grind)
    | exact superpose eq161971 eq98913
    | (have j0 := eq98913 y x
       grind)
    | exact resolve eq98913 eq161971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98913 eq161971
  have eq161990 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq161985
  have eq161997 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq161990
       have i₂ := eq113639
       grind)
    | exact superpose eq113639 eq161990
    | exact resolve eq161990 eq113639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161990
  have eq161998 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq161997
  have eq162003 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq161998
       grind)
    | exact superpose eq161998 eq16
    | exact resolve eq16 eq161998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161998
  have eq162219 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq161735 eq162003
    | exact resolve eq162003 eq161735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161735 eq162003
  have eq162220 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq162219
  have eq162257 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq162220
       grind)
    | exact superpose eq162220 eq10
    | exact resolve eq10 eq162220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162220
  have eq162447 : x = y ∨ x = y := by
    first
    | (have i₁ := eq162257
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq162257
    | exact resolve eq162257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162257
  have eq162448 : x = y := by grind
  clear eq162447
  have eq162463 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162448
       grind)
    | exact superpose eq162448 eq16
    | exact resolve eq16 eq162448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162448
  have eq162464 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq162463
       have i₂ := eq113459
       grind)
    | exact superpose eq113459 eq162463
    | exact resolve eq162463 eq113459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113459 eq162463
  have eq162465 : False := by grind
  exact eq162465

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq81
    | exact resolve eq81 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq81
  have eq108 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq109 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq108
    | exact resolve eq108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq109
  have eq239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq241 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq244 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq88 X1
       grind)
    | exact superpose eq88 eq239
    | (have j0 := eq239 X0 X1
       grind)
    | exact resolve eq239 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1955 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq241 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq241
    | exact resolve eq241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq2021 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1955 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1955
    | (have j0 := eq1955 X0 X1
       grind)
    | exact resolve eq1955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2619 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq244 x y
       grind)
    | exact superpose eq244 eq16
    | (have j1 := eq244 x y
       grind)
    | exact resolve eq16 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq7022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2619
       have i₂ := eq2021 x y
       grind)
    | exact superpose eq2021 eq2619
    | (have j1 := eq2021 x y
       grind)
    | (have r₁ := eq2619
       have r₂ := eq2021 x y
       grind)
    | (have r₁ := eq2619
       have r₂ := eq2021 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2619
       have r₂ := eq2021 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2619 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq2619
  have eq7023 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq7022
  have eq7025 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7023
       grind)
    | exact superpose eq7023 eq16
    | exact resolve eq16 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7023
  have eq7026 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7025
       have r₂ := eq88 x
       grind)
    | exact resolve eq7025 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq7028 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq10
    | exact resolve eq10 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7090 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7028
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7028
    | exact resolve eq7028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq7093 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7090
       grind)
    | exact superpose eq7090 eq16
    | exact resolve eq16 eq7090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7090
  have eq7094 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq7093
       have r₂ := eq88 x
       grind)
    | exact resolve eq7093 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq7093
  have eq7103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq7094
       grind)
    | exact superpose eq7094 eq112
    | exact resolve eq112 eq7094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7094
  have eq7146 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq7103
       have r₂ := eq16
       grind)
    | exact resolve eq7103 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7103
  have eq7165 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7146
       grind)
    | exact superpose eq7146 eq10
    | exact resolve eq10 eq7146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7146
  have eq7227 : x = (M.op y y) := by
    first
    | (have i₁ := eq7165
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7165
    | exact resolve eq7165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165
  have eq7240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq7227
       grind)
    | exact superpose eq7227 eq112
    | exact resolve eq112 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq7227
  have eq7283 : False := by grind
  exact eq7283
