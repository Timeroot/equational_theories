import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq74
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq100
    | exact resolve eq100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq101
  have eq152 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq152
    | (have j0 := eq152 X0 X1
       grind)
    | exact resolve eq152 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq778 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq778 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq778
    | (have j0 := eq778 X0 X1
       grind)
    | exact resolve eq778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq4579 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq157 x y
       grind)
    | exact superpose eq157 eq16
    | (have j1 := eq157 x y
       grind)
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq4837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4579
       have i₂ := eq824 y x
       grind)
    | exact superpose eq824 eq4579
    | (have j1 := eq824 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq4579
       have r₂ := eq824 y x
       grind)
    | (have r₁ := eq4579
       have r₂ := eq824 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4579
       have r₂ := eq824 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4579 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq4579
  have eq4838 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq4837
  have eq4840 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4838
       grind)
    | exact superpose eq4838 eq16
    | exact resolve eq16 eq4838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4838
  have eq4841 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4840
       have r₂ := eq81 x
       grind)
    | exact resolve eq4840 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840
  have eq4847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq4841
       grind)
    | exact superpose eq4841 eq104
    | exact resolve eq104 eq4841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841
  have eq4859 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4847
       have r₂ := eq16
       grind)
    | exact resolve eq4847 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4847
  have eq4862 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4859
       grind)
    | exact superpose eq4859 eq10
    | exact resolve eq10 eq4859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4913 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4862
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4862
    | exact resolve eq4862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862
  have eq4916 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4913
       grind)
    | exact superpose eq4913 eq16
    | exact resolve eq16 eq4913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq4917 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4916
       have r₂ := eq81 x
       grind)
    | exact resolve eq4916 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq4916
  have eq4924 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq4917
       grind)
    | exact superpose eq4917 eq10
    | exact resolve eq10 eq4917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq4975 : y = (M.op x x) := by
    first
    | (have i₁ := eq4924
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4924
    | exact resolve eq4924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq4987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq4975
       grind)
    | exact superpose eq4975 eq104
    | exact resolve eq104 eq4975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq4975
  have eq4998 : False := by grind
  exact eq4998

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq619 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq624 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq619 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq619
    | exact resolve eq619 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq633 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq624 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq624
    | (have j0 := eq624 x y
       grind)
    | exact resolve eq624 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq624
    | (have j0 := eq624 (σ x) (σ y)
       grind)
    | exact resolve eq624 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq633 eq14
    | exact resolve eq14 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq635 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq635
       grind)
    | exact resolve eq12 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq659
  have eq775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq775
    | exact resolve eq775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq779 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq776
       have r₂ := eq27
       grind)
    | exact resolve eq776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq781 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq779
    | exact resolve eq779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq783 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq781
    | exact resolve eq781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq785 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq783 eq27
    | exact resolve eq27 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq783 eq662
    | exact resolve eq662 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq794 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq783
  have eq863 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq793
       have r₂ := eq794
       grind)
    | exact resolve eq793 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq794
  have eq888 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq863 eq115
    | exact resolve eq115 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq863 eq83
    | exact resolve eq83 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq863
  have eq892 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq888
  have eq896 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq889
    | exact resolve eq889 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq889
  have eq897 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq892
       have r₂ := eq785
       grind)
    | exact resolve eq892 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq892
  have eq900 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq896
       have r₂ := eq75
       grind)
    | exact resolve eq896 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq896
  have eq903 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq897 eq51
    | exact resolve eq51 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq897 eq64
    | (have r₁ := eq64
       have r₂ := eq897
       grind)
    | exact resolve eq64 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq906 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq897 eq635
    | exact resolve eq635 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq910 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq904
  have eq913 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq624 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq903 x
       have i₂ := eq624 sF2 x
       grind)
    | exact superpose eq624 eq903
    | exact resolve eq903 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq940 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq900
       grind)
    | exact superpose eq900 eq72
    | exact resolve eq72 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq900
  have eq945 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq940
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq940
    | exact resolve eq940 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq966 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq945 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq967 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq966
  have eq971 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq967
    | exact resolve eq967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq974 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq971
    | exact resolve eq971 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq974
  have eq978 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq975 eq27
    | exact resolve eq27 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1087 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq910 eq115
    | exact resolve eq115 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq910
  have eq1090 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1087
  have eq1251 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq913
    | (have j0 := eq913 (σ y)
       grind)
    | exact resolve eq913 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq906 eq913
    | exact resolve eq913 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq913
  have eq1270 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1253
  have eq1277 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1270
    | exact resolve eq1270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1325 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1277 eq27
    | exact resolve eq27 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1600 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1277 eq1251
    | exact resolve eq1251 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1277
  have eq1624 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1600
  have eq1776 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1624 eq1090
    | exact resolve eq1090 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1624
  have eq1786 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1776
  have eq1796 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1786
       have r₂ := eq1325
       grind)
    | exact resolve eq1786 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325 eq1786
  have eq1800 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1796 eq20
    | exact resolve eq20 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1836 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1800
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1800
    | exact resolve eq1800 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1903 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1836 eq978
    | (have r₁ := eq978
       have r₂ := eq1836
       grind)
    | exact resolve eq978 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1921 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1903
  have eq1922 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1921
  have eq1945 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1922 eq51
    | exact resolve eq51 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1950 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1922 eq635
    | exact resolve eq635 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq1922
  have eq1969 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1945 X0
       have i₂ := eq624 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq1945 x
       have i₂ := eq624 sF2 x
       grind)
    | exact superpose eq624 eq1945
    | exact resolve eq1945 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq4579 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1950 eq1969
    | exact resolve eq1969 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950 eq1969
  have eq4614 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4579
  have eq4625 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4614
    | exact resolve eq4614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614
  have eq4631 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4625 eq27
    | exact resolve eq27 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq4668 : x = (M.op x y) := by
    first
    | (have r₁ := eq4631
       have r₂ := eq1836
       grind)
    | exact resolve eq4631 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq4631
  have eq4672 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4668 eq20
    | exact resolve eq20 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4694 : x = (M.op x x) := by
    first
    | exact superpose eq4668 eq633
    | exact resolve eq633 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq4696 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq4668 eq654
    | exact resolve eq654 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq4702 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq4696 X0
       have i₂ := eq624 x X0
       grind)
    | (have i₁ := eq4696 X0
       have i₂ := eq624 x (M.op x X0)
       grind)
    | exact superpose eq624 eq4696
    | exact resolve eq4696 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq4696
  have eq4721 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4672
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4672
    | exact resolve eq4672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4672
  have eq4724 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4721 eq26
    | exact resolve eq26 eq4721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4783 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq4694
       grind)
    | exact superpose eq4694 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq4694
       grind)
    | exact resolve eq13 eq4694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4796 : x = (k x x) := by grind
  clear eq4783
  have eq4997 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq4796
       grind)
    | exact superpose eq4796 eq43
    | exact resolve eq43 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4796
  have eq5001 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4721 eq4997
    | exact resolve eq4997 eq4721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4997
  have eq5002 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5001
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5001
    | exact resolve eq5001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001
  have eq5003 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4721 eq5002
    | exact resolve eq5002 eq4721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq5009 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5003 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5010 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5009
  have eq5077 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq4702 X0
       grind)
    | exact superpose eq4702 eq14
    | exact resolve eq14 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702
  have eq5098 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5077 X0
       have i₂ := eq4694
       grind)
    | exact superpose eq4694 eq5077
    | exact resolve eq5077 eq4694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4694 eq5077
  have eq5120 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5098 y
       grind)
    | exact superpose eq5098 eq18
    | (have j1 := eq5098 y
       grind)
    | exact resolve eq18 eq5098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5098
  have eq5164 : x = y := by
    first
    | exact superpose eq4668 eq5120
    | exact resolve eq5120 eq4668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4668 eq5120
  have eq5191 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5164
       grind)
    | exact superpose eq5164 eq24
    | exact resolve eq24 eq5164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5164
  have eq5242 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5191
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5191
    | exact resolve eq5191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5191
  have eq5259 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4721 eq5242
    | exact resolve eq5242 eq4721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4721 eq5242
  have eq5321 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5259 eq4724
    | exact resolve eq4724 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724 eq5259
  have eq5325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5010 eq5321
    | exact resolve eq5321 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5010 eq5321
  have eq5341 : False := by grind
  exact eq5341

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq40
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181
    | (have j0 := eq181 X0
       grind)
    | exact resolve eq181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq187 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq561 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq558
    | exact resolve eq558 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq809 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq846 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq862 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq39
    | exact resolve eq39 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq868 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq867
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq867
    | exact resolve eq867 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq870 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq868
    | exact resolve eq868 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq870 eq812
    | exact resolve eq812 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq885 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq878
       have r₂ := eq27
       grind)
    | exact resolve eq878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq892 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq885 eq16
    | exact resolve eq16 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (M.op (σ y) X0)) (M.op (σ x) X1)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq892 eq16
    | exact resolve eq16 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq939 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq885 eq920
    | exact resolve eq920 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (σ x) (M.op (σ y) X0)) (σ x)) (M.op (σ x) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq920 eq16
    | exact resolve eq16 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq947 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq948 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ x) (M.op (σ x) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq892 eq943
    | exact resolve eq943 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq943
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq948
    | (have j0 := eq948 (σ y)
       grind)
    | exact resolve eq948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq885 eq948
    | exact resolve eq948 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq954
  have eq969 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq964
    | exact resolve eq964 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1001 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq953 eq16
    | exact resolve eq16 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1005 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq969 eq1001
    | exact resolve eq1001 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq1001
  have eq1168 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1180 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1180
    | exact resolve eq1180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1258 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1005 eq947
    | exact resolve eq947 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1270 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1258
  have eq1297 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1270 eq1005
    | exact resolve eq1005 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1270
  have eq1304 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1297
  have eq1310 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq885 eq1304
    | exact resolve eq1304 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1334 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1310 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1310
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1310
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1310
       grind)
    | exact resolve eq13 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1310 eq16
    | exact resolve eq16 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1334
  have eq1345 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq561 eq1335
    | exact resolve eq1335 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq1335
  have eq1361 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1337 eq152
    | exact resolve eq152 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1337
  have eq1364 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1361
    | exact resolve eq1361 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1369 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq848 y
       have i₂ := eq1364
       grind)
    | exact superpose eq1364 eq848
    | (have j0 := eq848 y
       grind)
    | (have r₁ := eq848 y
       have r₂ := eq1364
       grind)
    | exact resolve eq848 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1370 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1369
  have eq1396 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ y)) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1345 eq176
    | exact resolve eq176 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1345 eq16
    | exact resolve eq16 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1406 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1310 eq1397
    | exact resolve eq1397 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1407 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1310 eq1396
    | exact resolve eq1396 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1406 eq1407
    | exact resolve eq1407 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq1407
  have eq1460 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1411 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1411
    | (have j0 := eq1411 x y
       grind)
    | exact resolve eq1411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1475 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq1411 X0 X1
       grind)
    | exact superpose eq1411 eq16
    | exact resolve eq16 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1556 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1411 (M.op X1 X1) X0
       have i₂ := eq1475 X1 X0
       grind)
    | exact superpose eq1475 eq1411
    | exact resolve eq1411 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1560 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1921 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq885 eq862
    | exact resolve eq862 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1560 (M.op X0 X0) X0
       have i₂ := eq862 X0
       grind)
    | exact superpose eq862 eq1560
    | (have j1 := eq862 X0
       grind)
    | exact resolve eq1560 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq1560
  have eq1952 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1930 X0
       have j1 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq1930 X0
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1930 X0
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1930 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | exact resolve eq1930 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1961 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1921
    | exact resolve eq1921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1962 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1961
  have eq1975 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq870 eq1962
    | exact resolve eq1962 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962
  have eq1979 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1310 eq1975
    | exact resolve eq1975 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2867 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163 (M.op sF1 sF1)
       have i₂ := eq1952 sF1
       grind)
    | exact superpose eq1952 eq163
    | exact resolve eq163 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq2868 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq1952 sF2
       grind)
    | exact superpose eq1952 eq141
    | exact resolve eq141 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq2884 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq885 eq2868
    | exact resolve eq2868 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq2868
  have eq2885 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1979 eq2867
    | exact resolve eq2867 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq2867
  have eq2890 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2884
    | exact resolve eq2884 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq2891 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1310 eq2885
    | exact resolve eq2885 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq2885
  have eq2894 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq809 eq2890
    | exact resolve eq2890 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq2890
  have eq2895 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2891
    | exact resolve eq2891 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891
  have eq2896 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2894 eq2895
    | exact resolve eq2895 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq2973 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2896 eq847
    | (have j0 := eq847 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq847 (M.op x y) (M.op x y)
       have r₂ := eq2896
       grind)
    | exact resolve eq847 eq2896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2974 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq2973
  have eq2975 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq2974
  have eq3326 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2975 eq1475
    | exact resolve eq1475 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq2975
  have eq3338 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3326 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq4481 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1184 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1184
    | (have j0 := eq1184 x y
       grind)
    | exact resolve eq1184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4488 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1184 x x
       have i₂ := eq2894
       grind)
    | exact superpose eq2894 eq1184
    | exact resolve eq1184 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq4489 : ∀ X0 : G, y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1184 x x
       have i₂ := eq3338 X0
       grind)
    | exact superpose eq3338 eq1184
    | (have j1 := eq3338 X0
       grind)
    | exact resolve eq1184 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq4566 : ∀ X0 : G, y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4489 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4489
    | (have j0 := eq4489 X0
       grind)
    | exact resolve eq4489 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq4567 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4488
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4488
    | exact resolve eq4488 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4488
  have eq4568 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4567
  have eq4577 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4568 eq175
    | exact resolve eq175 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4578 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4568 eq179
    | (have r₁ := eq179
       have r₂ := eq4568
       grind)
    | exact resolve eq179 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4581 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4578
  have eq4583 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4577 X0
       have i₂ := eq1184 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq4577 x
       have i₂ := eq1184 sF2 x
       grind)
    | exact superpose eq1184 eq4577
    | exact resolve eq4577 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq4577
  have eq4625 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4583
    | (have j0 := eq4583 (σ y)
       grind)
    | exact resolve eq4583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4638 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4583 eq176
    | exact resolve eq176 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4639 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4583 eq16
    | exact resolve eq16 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583
  have eq4661 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4639
    | (have j0 := eq4639 X0
       grind)
    | exact resolve eq4639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639
  have eq4662 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq4638
    | (have j0 := eq4638 X0 X1
       grind)
    | exact resolve eq4638 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4668 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4568 eq4625
    | exact resolve eq4625 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq4670 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4568 eq4661
    | exact resolve eq4661 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661
  have eq4671 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4568 eq4662
    | exact resolve eq4662 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq4675 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4668
    | exact resolve eq4668 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4668
  have eq4676 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4670 eq4671
    | exact resolve eq4671 eq4670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4680 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4568 eq4675
    | exact resolve eq4675 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq4687 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4680 eq31
    | exact resolve eq31 eq4680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4790 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4687
    | exact resolve eq4687 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4687
  have eq4808 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1370
       have i₂ := eq4790
       grind)
    | exact superpose eq4790 eq1370
    | exact resolve eq1370 eq4790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq4790
  have eq4902 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4808
  have eq4979 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4566 eq4902
    | (have j1 := eq4566 (M.op x y)
       grind)
    | exact resolve eq4902 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566 eq4902
  have eq4980 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq4979
  have eq5040 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4670 eq4581
    | exact resolve eq4581 eq4670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4581 eq4670
  have eq5071 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5040
  have eq5099 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4680 eq5071
    | exact resolve eq5071 eq4680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680 eq5071
  have eq5144 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5099 eq141
    | exact resolve eq141 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5099
  have eq5176 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5144
    | exact resolve eq5144 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq5331 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847 x x
       have i₂ := eq5176
       grind)
    | exact superpose eq5176 eq847
    | (have j0 := eq847 x x
       grind)
    | (have r₁ := eq847 x x
       have r₂ := eq5176
       grind)
    | exact resolve eq847 eq5176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176
  have eq5332 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5331
  have eq5333 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5332
  have eq5615 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq4676 X0 X1
       grind)
    | exact superpose eq4676 eq16
    | exact resolve eq16 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6328 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5615 x X0
       have i₂ := eq5333
       grind)
    | exact superpose eq5333 eq5615
    | exact resolve eq5615 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5333 eq5615
  have eq6397 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6328
  have eq6474 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6397 y
       grind)
    | exact superpose eq6397 eq18
    | (have j1 := eq6397 y
       grind)
    | exact resolve eq18 eq6397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6493 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4676 x X0
       have i₂ := eq6397 X0
       grind)
    | exact superpose eq6397 eq4676
    | (have j1 := eq6397 y
       grind)
    | exact resolve eq4676 eq6397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676 eq6397
  have eq6502 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6493
  have eq6508 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6474
  have eq6552 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6508
       grind)
    | exact superpose eq6508 eq24
    | exact resolve eq24 eq6508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6677 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6552
    | exact resolve eq6552 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552
  have eq6728 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op y X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1168 x X0
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq1168
    | exact resolve eq1168 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq6769 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1168 eq176
    | exact resolve eq176 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6787 : ∀ X2 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq6769 x x X2
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq6769
    | exact resolve eq6769 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6769
  have eq6805 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6502 eq6728
    | (have j1 := eq6502 (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y))
       grind)
    | exact resolve eq6728 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502 eq6728
  have eq6823 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6787 eq6805
    | exact resolve eq6805 eq6787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6787 eq6805
  have eq6824 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6823
  have eq6942 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6824 eq174
    | exact resolve eq174 eq6824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6824
  have eq6962 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4568 eq6942
    | exact resolve eq6942 eq4568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4568 eq6942
  have eq7225 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq6962
       have i₂ := eq11 sF0 (M.op x x)
       grind)
    | exact superpose eq11 eq6962
    | (have j1 := eq11 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq6962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7233 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6962 eq11
    | (have j0 := eq11 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq11 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq7270 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7233 eq7225
    | exact resolve eq7225 eq7233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225 eq7233
  have eq7279 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4980 eq7270
    | exact resolve eq7270 eq4980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7270
  have eq7283 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq848 (M.op x y)
       grind)
    | (have r₁ := eq7279
       have r₂ := eq848 (M.op x y)
       grind)
    | exact resolve eq7279 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq7279
  have eq7285 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4980 eq7283
    | exact resolve eq7283 eq4980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4980 eq7283
  have eq7286 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7285
  have eq7300 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7286 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq7286
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7286
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7286
       grind)
    | exact resolve eq13 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7301 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7286 eq16
    | exact resolve eq16 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7316 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7300
  have eq7330 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq184 eq7301
    | exact resolve eq7301 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq7301
  have eq7343 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7316 eq41
    | exact resolve eq41 eq7316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq7316
  have eq7355 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7343
    | exact resolve eq7343 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7343
  have eq7357 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6677 eq7355
    | exact resolve eq7355 eq6677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7355
  have eq7383 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7357 eq847
    | (have j0 := eq847 (σ y) (σ y)
       grind)
    | (have r₁ := eq847 (σ y) (σ y)
       have r₂ := eq7357
       grind)
    | exact resolve eq847 eq7357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7357
  have eq7384 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7383
  have eq7385 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7384
  have eq7554 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f7554_14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
      intro X0 X1 X2 X3
      grind
    have f7554_15 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f7554_23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f7554_24 : X0 ≠ (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) := by grind
    have f7554_25 : x ≠ (M.op x y) := by grind
    have f7554_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f7554_28 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f7554_15 X0
         grind)
      | (have r₁ := f7554_15 X0
         have r₂ := f7554_25
         grind)
      | exact resolve f7554_15 f7554_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_29 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
      intro X0
      first
      | (have j0 := f7554_28 X0
         grind)
      | (have r₁ := f7554_28 X0
         have r₂ := f7554_26
         grind)
      | exact resolve f7554_28 f7554_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_55 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f7554_23 X0 (M.op x y) (M.op x y)
         have i₂ := f7554_29 X0
         grind)
      | exact superpose f7554_29 f7554_23
      | exact resolve f7554_23 f7554_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_74 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X1)) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f7554_14 X0 (M.op x y) (M.op x y) X1
         have i₂ := f7554_29 X0
         grind)
      | exact superpose f7554_29 f7554_14
      | exact resolve f7554_14 f7554_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_85 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f7554_74 X0 X1
         have i₂ := f7554_55 (M.op X0 X1)
         grind)
      | exact superpose f7554_55 f7554_74
      | exact resolve f7554_74 f7554_55
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f7554_23 X1 X0 X0
         have i₂ := f7554_85 X0 X1
         grind)
      | exact superpose f7554_85 f7554_23
      | exact resolve f7554_23 f7554_85
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_166 : X0 ≠ (M.op (M.op X0 X1) X0) := by
      first
      | (have i₁ := f7554_24
         have i₂ := f7554_99 (M.op x y) (M.op X0 X1)
         grind)
      | exact superpose f7554_99 f7554_24
      | exact resolve f7554_24 f7554_99
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7554_183 : False := by
      first
      | (have r₁ := f7554_166
         have r₂ := f7554_85 X0 X1
         grind)
      | exact resolve f7554_166 f7554_85
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f7554_183
  clear eq176
  have eq7555 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7330 eq16
    | exact resolve eq16 eq7330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7330
  have eq7584 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7286 eq7555
    | exact resolve eq7555 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7555
  have eq7585 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7286 eq7554
    | exact resolve eq7554 eq7286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7286 eq7554
  have eq7593 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7584 eq7585
    | exact resolve eq7585 eq7584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584 eq7585
  have eq7948 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq7593 X0 X1
       grind)
    | exact superpose eq7593 eq16
    | exact resolve eq16 eq7593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8168 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7385 eq7948
    | exact resolve eq7948 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7385 eq7948
  have eq8221 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8334 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8221 eq7593
    | exact resolve eq7593 eq8221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7593 eq8221
  have eq8345 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334
  have eq8449 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8345 eq26
    | (have j1 := eq8345 (σ x)
       grind)
    | exact resolve eq26 eq8345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8345
  have eq8528 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8449 eq27
    | exact resolve eq27 eq8449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8449
  have eq8545 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8528
       have r₂ := eq6677
       grind)
    | exact resolve eq8528 eq6677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677 eq8528
  have eq8547 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8545 eq27
    | exact resolve eq27 eq8545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8549 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8545 eq179
    | (have r₁ := eq179
       have r₂ := eq8545
       grind)
    | exact resolve eq179 eq8545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq8552 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8545 eq1174
    | exact resolve eq1174 eq8545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq8545
  have eq8553 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8549
  have eq8555 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8552 x x
       have i₂ := eq16 sF2 x x
       grind)
    | exact superpose eq16 eq8552
    | exact resolve eq8552 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8552
  have eq8585 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8555 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq8555
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8555
       grind)
    | exact resolve eq13 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8603 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8585
  have eq8659 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8603 eq141
    | exact resolve eq141 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq8603
  have eq8692 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8659
    | exact resolve eq8659 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8659
  have eq8726 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847 x x
       have i₂ := eq8692
       grind)
    | exact superpose eq8692 eq847
    | (have j0 := eq847 x x
       grind)
    | (have r₁ := eq847 x x
       have r₂ := eq8692
       grind)
    | exact resolve eq847 eq8692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq8692
  have eq8727 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8726
  have eq8728 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8727
  have eq8921 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8553 eq8555
    | exact resolve eq8555 eq8553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8553 eq8555
  have eq8971 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8921
  have eq8990 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8971 eq870
    | exact resolve eq870 eq8971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq8971
  have eq9008 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8990
  have eq9018 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9008
       have r₂ := eq8547
       grind)
    | exact resolve eq9008 eq8547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8547 eq9008
  have eq9023 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6508 eq9018
    | exact resolve eq9018 eq6508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508 eq9018
  have eq9062 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8728
       have i₂ := eq9023
       grind)
    | exact superpose eq9023 eq8728
    | exact resolve eq8728 eq9023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728 eq9023
  have eq9100 : x = (M.op x y) := by grind
  clear eq9062
  have eq9126 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9100
       grind)
    | exact superpose eq9100 eq18
    | exact resolve eq18 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9127 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9100
       grind)
    | exact superpose eq9100 eq22
    | exact resolve eq22 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9133 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1168 X0 X1
       have i₂ := eq9100
       grind)
    | exact superpose eq9100 eq1168
    | exact resolve eq1168 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq9100
  have eq9135 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq9133 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq9133
    | exact resolve eq9133 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9139 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9127 eq20
    | exact resolve eq20 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9261 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq9126 eq174
    | exact resolve eq174 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq9281 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq4481 eq9261
    | exact resolve eq9261 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481 eq9261
  have eq9286 : y = (M.op x y) := by
    first
    | exact superpose eq9126 eq9281
    | exact resolve eq9281 eq9126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9126 eq9281
  have eq9292 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9286
       grind)
    | exact superpose eq9286 eq24
    | exact resolve eq24 eq9286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9286
  have eq9355 : (σ x) = (σ y) := by
    first
    | exact superpose eq9127 eq9292
    | exact resolve eq9292 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127 eq9292
  have eq9357 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9355 eq26
    | exact resolve eq26 eq9355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9355
  have eq9474 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9135 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq9135
       grind)
    | exact resolve eq13 eq9135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9135
  have eq9488 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq9474
  have eq9504 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq9488 eq37
    | exact resolve eq37 eq9488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9488
  have eq9518 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq9504
    | exact resolve eq9504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9504
  have eq9520 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9139 eq9518
    | exact resolve eq9518 eq9139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq9590 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9357 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9357
  have eq9605 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9590
  have eq9608 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9520 eq9605
    | exact resolve eq9605 eq9520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9520 eq9605
  have eq9609 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9608
  have eq9614 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9609 eq27
    | exact resolve eq27 eq9609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9609
  have eq9625 : False := by grind
  exact eq9625

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  clear eq22
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq44
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq107
    | exact resolve eq107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq420 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq423 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq420 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq420
    | exact resolve eq420 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq108 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | exact resolve eq75 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq681
    | exact resolve eq681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq685 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq682
       have r₂ := eq27
       grind)
    | exact resolve eq682 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq690 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq685 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq685
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq685
       grind)
    | exact resolve eq13 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq694 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq690
  have eq734 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq694 eq85
    | exact resolve eq85 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq694
  have eq738 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq734
    | exact resolve eq734 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq734
  have eq741 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75 y y
       have i₂ := eq738
       grind)
    | exact superpose eq738 eq75
    | (have j0 := eq75 x y
       grind)
    | exact resolve eq75 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq742 : y = (M.op y y) := by grind
  clear eq741
  have eq766 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq742
       grind)
    | exact superpose eq742 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq742
       grind)
    | exact resolve eq13 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq742
       grind)
    | exact superpose eq742 eq14
    | exact resolve eq14 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : y = (k y y) := by grind
  clear eq766
  have eq771 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq767 X0
       have i₂ := eq423 y X0
       grind)
    | (have i₁ := eq767 X0
       have i₂ := eq423 y (M.op y X0)
       grind)
    | exact superpose eq423 eq767
    | exact resolve eq767 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq767
  have eq779 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq770
       grind)
    | exact superpose eq770 eq73
    | exact resolve eq73 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq770
  have eq783 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq779
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq779
    | exact resolve eq779 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq803 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq783 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | exact resolve eq75 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq783
  have eq804 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq803
  have eq828 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq771 X0
       grind)
    | exact superpose eq771 eq14
    | exact resolve eq14 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq828 X0
       have i₂ := eq742
       grind)
    | exact superpose eq742 eq828
    | exact resolve eq828 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq828
  have eq840 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq771 X0
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq771
    | exact resolve eq771 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq850 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1
       have i₂ := eq836 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq836 eq14
    | exact resolve eq14 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq850
    | exact resolve eq850 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq850
  have eq864 : y = (M.op x y) := by
    first
    | (have i₁ := eq840 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq840
    | (have j0 := eq840 x
       grind)
    | exact resolve eq840 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq840
  have eq906 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq864 eq20
    | exact resolve eq20 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq864
  have eq930 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq906
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq906
    | exact resolve eq906 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq906
  have eq934 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq930 eq26
    | exact resolve eq26 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1128 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq854 X0 X1
       grind)
    | exact superpose eq854 eq14
    | exact resolve eq14 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq804 eq1128
    | exact resolve eq1128 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq1128
  have eq1212 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq930 eq1182
    | exact resolve eq1182 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq1182
  have eq1225 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1212 eq854
    | exact resolve eq854 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq1212
  have eq1265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1225 eq934
    | exact resolve eq934 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq1225
  have eq1276 : False := by grind
  exact eq1276

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  clear eq22
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq10
    | exact resolve eq10 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq184 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq359 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq370 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq370 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq370
    | exact resolve eq370 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq374 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq376 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq359 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq359
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq437 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) ≠ (M.op X0 X3) ∨ (M.op X0 X3) = (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq443 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op X0 X3) = (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq437 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq437
    | (have j0 := eq437 X0 X1 X2 X3
       grind)
    | exact resolve eq437 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq446 : ∀ X0 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op X0 X3) = (k (M.op X0 X3) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq443 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq443
    | (have j0 := eq443 X0 x x X3
       grind)
    | exact resolve eq443 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq3077 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq374 eq52
    | exact resolve eq52 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3093 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3077 eq374
    | exact resolve eq374 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq3077
  have eq3110 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3093 eq14
    | exact resolve eq14 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq3122 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3110 X0
       have i₂ := eq373 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3110 x
       have i₂ := eq373 (M.op sF4 sF4) x
       grind)
    | exact superpose eq373 eq3110
    | exact resolve eq3110 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3248 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq376 X0 X0 x
       grind)
    | exact superpose eq376 eq52
    | exact resolve eq52 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3289 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq376 X0 X0 X0
       have i₂ := eq3248 X0
       grind)
    | exact superpose eq3248 eq376
    | exact resolve eq376 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq3421 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq446 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq3289 X0
       grind)
    | exact superpose eq3289 eq446
    | (have r₁ := eq446 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq3289 X0
       grind)
    | exact resolve eq446 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq3422 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq4098 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184
    | (have j0 := eq184 y
       grind)
    | exact resolve eq184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq4112 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4098
  have eq4116 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4112
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq4112
    | exact resolve eq4112 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4139 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4116
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq4154 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4139 eq104
    | exact resolve eq104 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq14297 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq4139 eq102
    | exact resolve eq102 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq14299 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4139 eq105
    | exact resolve eq105 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq17890 : (σ (k (k y y) (k y y))) = (k (k (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq14297 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq14297
    | exact resolve eq14297 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq14297
  have eq17935 : (σ (k (k y y) (k y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4139 eq17890
    | exact resolve eq17890 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq17890
  have eq17958 : (M.op (σ y) (σ y)) = (σ (k (k y y) (k y y))) := by
    first
    | (have i₁ := eq17935
       have i₂ := eq3422 sF3
       grind)
    | exact superpose eq3422 eq17935
    | exact resolve eq17935 eq3422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17935
  have eq18357 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq14299
       grind)
    | exact superpose eq14299 eq16
    | exact resolve eq16 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14299
  have eq18417 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4154 eq18357
    | exact resolve eq18357 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18357
  have eq18422 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq18417
       have r₂ := eq13 y y
       grind)
    | exact resolve eq18417 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18417
  have eq18431 : (M.op (σ y) (σ y)) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq17958
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq17958
    | exact resolve eq17958 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958
  have eq18451 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq18431
       have i₂ := eq3422 y
       grind)
    | exact superpose eq3422 eq18431
    | exact resolve eq18431 eq3422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422 eq18431
  have eq22488 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3122 eq14
    | exact resolve eq14 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq22543 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22488 X0
       have i₂ := eq3289 sF4
       grind)
    | exact superpose eq3289 eq22488
    | exact resolve eq22488 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289 eq22488
  have eq22643 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq22543 eq376
    | exact resolve eq376 eq22543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq22672 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq22543 eq22643
    | exact resolve eq22643 eq22543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22543 eq22643
  have eq23283 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq22672 X0 X1
       grind)
    | exact superpose eq22672 eq14
    | exact resolve eq14 eq22672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq27425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq27424
    | exact resolve eq27424 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27424
  have eq27436 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq27425
       have r₂ := eq27
       grind)
    | exact resolve eq27425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27425
  have eq27440 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27436 eq4154
    | exact resolve eq4154 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27436
  have eq27526 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27440
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq27440
    | exact resolve eq27440 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27440
  have eq27544 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq27526
    | exact resolve eq27526 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27526
  have eq27545 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq27544
  have eq27575 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27545 eq373
    | exact resolve eq373 eq27545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27545
  have eq27625 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27575 eq4154
    | exact resolve eq4154 eq27575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154 eq27575
  have eq27711 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27625
       have i₂ := eq18422
       grind)
    | exact superpose eq18422 eq27625
    | exact resolve eq27625 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18422 eq27625
  have eq27729 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq27711
    | exact resolve eq27711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27711
  have eq27730 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq27729
  have eq27758 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23283 y X0
       have i₂ := eq27730
       grind)
    | exact superpose eq27730 eq23283
    | exact resolve eq23283 eq27730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27730
  have eq27971 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq373 y x
       have i₂ := eq27758 X0
       grind)
    | exact superpose eq27758 eq373
    | (have j1 := eq27758 y
       grind)
    | exact resolve eq373 eq27758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq27758
  have eq28140 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq27971 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27971
  have eq28141 : y = (M.op y y) := by grind
  clear eq28140
  have eq28199 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18451
       have i₂ := eq28141
       grind)
    | exact superpose eq28141 eq18451
    | exact resolve eq18451 eq28141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451
  have eq28218 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23283 y X0
       have i₂ := eq28141
       grind)
    | exact superpose eq28141 eq23283
    | exact resolve eq23283 eq28141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28141
  have eq28282 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq28199
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28199
    | exact resolve eq28199 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28199
  have eq28349 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22672 y X0
       have i₂ := eq28218 X0
       grind)
    | exact superpose eq28218 eq22672
    | exact resolve eq22672 eq28218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28218
  have eq28468 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28282 eq23283
    | exact resolve eq23283 eq28282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23283 eq28282
  have eq28948 : y = (M.op x y) := by
    first
    | (have i₁ := eq28349 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28349
    | (have j0 := eq28349 x
       grind)
    | exact resolve eq28349 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28349
  have eq29203 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq28948 eq20
    | exact resolve eq20 eq28948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28948
  have eq29395 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29203
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29203
    | exact resolve eq29203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29203
  have eq30155 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq29395 eq26
    | exact resolve eq26 eq29395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30409 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq29395 eq28468
    | exact resolve eq28468 eq29395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28468 eq29395
  have eq30453 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30409 eq22672
    | exact resolve eq22672 eq30409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22672 eq30409
  have eq32728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30453 eq30155
    | exact resolve eq30155 eq30453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30155 eq30453
  have eq32729 : False := by grind
  exact eq32729

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  clear eq36
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq73
    | (have j1 := eq67 x x
       grind)
    | exact resolve eq73 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq346 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq354 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq351 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95 eq67
    | (have j0 := eq67 x (σ x)
       grind)
    | exact resolve eq67 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq699
    | exact resolve eq699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq703 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq700
       have r₂ := eq27
       grind)
    | exact resolve eq700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq709 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq703 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq703
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq703
       grind)
    | exact resolve eq13 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq713 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq709
  have eq736 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq713 eq49
    | exact resolve eq49 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq713
  have eq740 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq736
    | exact resolve eq736 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq736
  have eq743 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67 x x
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq67
    | (have j0 := eq67 x x
       grind)
    | exact resolve eq67 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq744 : x = (M.op x x) := by grind
  clear eq743
  have eq767 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq744
       grind)
    | exact resolve eq13 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq14
    | exact resolve eq14 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : x = (k x x) := by grind
  clear eq767
  have eq772 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq768 X0
       have i₂ := eq354 x X0
       grind)
    | (have i₁ := eq768 X0
       have i₂ := eq354 x (M.op x X0)
       grind)
    | exact superpose eq354 eq768
    | exact resolve eq768 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq768
  have eq778 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq771
       grind)
    | exact superpose eq771 eq43
    | exact resolve eq43 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq771
  have eq782 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq778
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq778
    | exact resolve eq778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq778
  have eq785 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq782 eq67
    | (have j0 := eq67 x (σ x)
       grind)
    | exact resolve eq67 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq782
  have eq786 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq785
  have eq803 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq772 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq772
    | (have j0 := eq772 y
       grind)
    | exact resolve eq772 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq14
    | exact resolve eq14 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq809 X0
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq809
    | exact resolve eq809 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq823 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq803 eq50
    | exact resolve eq50 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq803
  have eq830 : y = (M.op x y) := by
    first
    | (have i₁ := eq823
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq823
    | exact resolve eq823 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq833 : y = (M.op x y) := by
    first
    | (have i₁ := eq830
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq830
    | exact resolve eq830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq830
  have eq834 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq833 eq20
    | exact resolve eq20 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq833
  have eq860 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq834
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq834
    | exact resolve eq834 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq834
  have eq862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq860 eq26
    | exact resolve eq26 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1014 : (σ x) = (M.op (M.op (M.op x x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq346 x x
       have i₂ := eq772 sF2
       grind)
    | exact superpose eq772 eq346
    | exact resolve eq346 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq772
  have eq1032 : (σ x) = (M.op (M.op x (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1014
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq1014
    | exact resolve eq1014 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq1014
  have eq1037 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq816 sF4
       grind)
    | exact superpose eq816 eq1032
    | exact resolve eq1032 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq1032
  have eq1041 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1037 eq51
    | exact resolve eq51 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1037
  have eq1049 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq860 eq1041
    | exact resolve eq1041 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq1041
  have eq1052 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq786 eq1049
    | exact resolve eq1049 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq1049
  have eq1054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq862 eq1052
    | exact resolve eq1052 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq1052
  have eq1055 : False := by grind
  exact eq1055

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq88 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq162 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq162 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq162
    | (have j0 := eq162 X0
       grind)
    | exact resolve eq162 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq162
  have eq175 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | (have j0 := eq174 X0
       grind)
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq176 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq175 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq175 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq175 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq183 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq176 (σ X0)
       grind)
    | exact superpose eq176 eq15
    | exact resolve eq15 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq176 (τ X0)
       grind)
    | exact superpose eq176 eq35
    | exact resolve eq35 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq188 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq185
    | exact resolve eq185 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq190 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq183
    | exact resolve eq183 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq183
  have eq230 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq465 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 X0 x X0
       have i₂ := eq95 X0 X0 x
       grind)
    | exact superpose eq95 eq20
    | exact resolve eq20 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq465 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq465
    | exact resolve eq465 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq503 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 X0 X0 X0
       have i₂ := eq480 X0
       grind)
    | exact superpose eq480 eq95
    | exact resolve eq95 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq627 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq503 X0
       grind)
    | exact superpose eq503 eq95
    | exact resolve eq95 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq645 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq627
    | exact resolve eq627 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq627
  have eq980 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) (M.op X1 X3)) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93 X1 (M.op X0 X0) (M.op X0 X0) X2 X3
       have i₂ := eq645 X0 X1
       grind)
    | exact superpose eq645 eq93
    | exact resolve eq93 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq984 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq645 X0 X1
       grind)
    | exact superpose eq645 eq20
    | exact resolve eq20 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq985 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq645 X0 X1
       grind)
    | exact superpose eq645 eq9
    | exact resolve eq9 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq503 X0
       grind)
    | exact superpose eq503 eq985
    | exact resolve eq985 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1001 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq984 X0 X1 X2
       have i₂ := eq503 X0
       grind)
    | exact superpose eq503 eq984
    | exact resolve eq984 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq1004 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X1 X3)) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq980 X0 X1 X2 X3
       have i₂ := eq503 X0
       grind)
    | exact superpose eq503 eq980
    | exact resolve eq980 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq980
  have eq1006 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1001 x X1 X2
       have i₂ := eq1000 x (M.op X1 X2)
       grind)
    | exact superpose eq1000 eq1001
    | exact resolve eq1001 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1008 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X1) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1004 x X1 X2 X3
       have i₂ := eq1000 x (M.op X1 X2)
       grind)
    | exact superpose eq1000 eq1004
    | exact resolve eq1004 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1012 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 (σ X0) X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq1000
    | exact resolve eq1000 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 (τ X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq1000
    | exact resolve eq1000 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1015 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X1 X0
       have i₂ := eq1000 X1 X0
       grind)
    | exact superpose eq1000 eq645
    | exact resolve eq645 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1006 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1006
    | exact resolve eq1006 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 (τ (M.op X1 X1)) X0
       have i₂ := eq1014 X1 X0
       grind)
    | exact superpose eq1014 eq1006
    | exact resolve eq1006 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq230
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq230
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq230
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq230
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq230 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq1881 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1880
  have eq1921 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1008 (M.op X0 X1) X2 X0
       have i₂ := eq1006 X0 X1
       grind)
    | exact superpose eq1006 eq1008
    | exact resolve eq1008 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq24531 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq16
    | exact resolve eq16 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881
  have eq24532 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24531
       have r₂ := eq190 x
       grind)
    | exact resolve eq24531 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24531
  have eq30348 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq498 X0 X0 X1 X2
       grind)
    | exact superpose eq498 eq9
    | exact resolve eq9 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq30473 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30348 X0 X1 X2
       have i₂ := eq1000 X0 X1
       grind)
    | exact superpose eq1000 eq30348
    | exact resolve eq30348 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq30348
  have eq30695 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30473 (M.op (M.op (M.op X0 X1) X2) X0) X3 (M.op X0 X1)
       have i₂ := eq1921 X0 X1 X2
       grind)
    | exact superpose eq1921 eq30473
    | exact resolve eq30473 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq30696 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30473 (M.op X0 X1) X2 X0
       have i₂ := eq1006 X0 X1
       grind)
    | exact superpose eq1006 eq30473
    | exact resolve eq30473 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30776 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) (M.op X1 X0) X0
       have i₂ := eq30473 X1 X0 X2
       grind)
    | exact superpose eq30473 eq9
    | exact resolve eq9 eq30473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30473
  have eq30954 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2))) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30696 (M.op X1 (M.op (M.op X1 X0) X2)) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq30696
    | exact resolve eq30696 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31078 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 X2) X0) X0
       have i₂ := eq30696 X1 X2 X0
       grind)
    | exact superpose eq30696 eq9
    | exact resolve eq9 eq30696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30696
  have eq31814 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op X0 X2) X2) X3) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30776 X0 (M.op (M.op X1 X0) X0) (M.op X1 X2)
       have i₂ := eq30776 X0 X1 X2
       grind)
    | exact superpose eq30776 eq30776
    | exact resolve eq30776 eq30776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105036 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3)) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30954 (M.op (M.op (M.op X0 X1) X1) X2) X0 X3 X2
       have i₂ := eq31814 X0 (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X1) X2)) X3) X1 X2
       grind)
    | exact superpose eq31814 eq30954
    | exact resolve eq30954 eq31814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30954 eq31814
  have eq107280 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X3))
       have i₂ := eq1142 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq1142 eq9
    | exact resolve eq9 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq107967 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op (M.op X0 X2) (M.op X1 X3)) X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107280 (M.op (M.op X0 X2) (M.op X1 X3)) X1 X3 X0
       have i₂ := eq31078 (M.op X1 X3) X0 X2
       grind)
    | exact superpose eq31078 eq107280
    | exact resolve eq107280 eq31078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31078
  have eq128177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107967 (M.op (M.op (M.op X0 X1) X2) X0) X0 (M.op (M.op (M.op X0 X1) X2) X0) X1
       have i₂ := eq30695 X0 X1 X2 (M.op (M.op (M.op X0 X1) X2) X0)
       grind)
    | exact superpose eq30695 eq107967
    | exact resolve eq107967 eq30695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30695 eq107967
  have eq129354 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op X1 X0) X2) X1)) X3) X3) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30776 X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X0)) X1
       have i₂ := eq128177 X0 X1 X2
       grind)
    | exact superpose eq128177 eq30776
    | exact resolve eq30776 eq128177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30776 eq128177
  have eq155554 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op (M.op X1 X2) X2) X0)) (M.op X1 X0)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107280 X1 (M.op X1 (M.op (M.op (M.op X1 X2) X2) X0)) X3 X0
       have i₂ := eq105036 X1 X2 X0 X3
       grind)
    | exact superpose eq105036 eq107280
    | exact resolve eq107280 eq105036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105036 eq107280
  have eq520602 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24532
       grind)
    | exact superpose eq24532 eq10
    | exact resolve eq10 eq24532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24532
  have eq520807 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520602
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq520602
    | exact resolve eq520602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520602
  have eq521970 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq520807
       grind)
    | exact superpose eq520807 eq16
    | exact resolve eq16 eq520807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520807
  have eq521971 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq521970
       have r₂ := eq190 x
       grind)
    | exact resolve eq521970 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq521970
  have eq522032 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1006 x y
       have i₂ := eq521971
       grind)
    | exact superpose eq521971 eq1006
    | exact resolve eq1006 eq521971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521971
  have eq523516 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) X0) X0) (σ y))) (σ x)) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq155554 (σ y) (σ x) X0 X1
       have i₂ := eq522032
       grind)
    | exact superpose eq522032 eq155554
    | exact resolve eq155554 eq522032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155554 eq522032
  have eq523723 : ∀ X1 : G, x = (M.op x x) ∨ (M.op (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq523516 x X1
       have i₂ := eq1006 (σ x) (M.op (M.op (M.op (σ x) x) x) (σ y))
       grind)
    | exact superpose eq1006 eq523516
    | exact resolve eq523516 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq523516
  have eq523979 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 X0 x
       have i₂ := eq523723 X1
       grind)
    | exact superpose eq523723 eq1015
    | (have j1 := eq523723 X1
       grind)
    | exact resolve eq1015 eq523723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq523723
  have eq526826 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq1324 X0 (σ x)
       have i₂ := eq523979 X0 (σ x)
       grind)
    | exact superpose eq523979 eq1324
    | (have j1 := eq523979 X1 X1
       grind)
    | exact resolve eq1324 eq523979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324 eq523979
  have eq527912 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq526826 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq526826
    | (have j0 := eq526826 X0 X0
       grind)
    | exact resolve eq526826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526826
  have eq532637 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq527912 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527912
  have eq532638 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq532637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532637
  have eq532690 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1012 x X0
       have i₂ := eq532638 x
       grind)
    | exact superpose eq532638 eq1012
    | exact resolve eq1012 eq532638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq533567 : ∀ X1 : G, (M.op x X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq129354 X1 x x x
       have i₂ := eq532638 (M.op (M.op x (M.op (M.op (M.op x X1) x) x)) x)
       grind)
    | exact superpose eq532638 eq129354
    | exact resolve eq129354 eq532638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129354 eq532638
  have eq537089 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532690 (σ y)
       grind)
    | exact superpose eq532690 eq16
    | exact resolve eq16 eq532690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532690
  have eq538566 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq537089
       have i₂ := eq533567 y
       grind)
    | (have i₁ := eq537089
       have i₂ := eq533567 (M.op x y)
       grind)
    | exact superpose eq533567 eq537089
    | exact resolve eq537089 eq533567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533567 eq537089
  have eq538567 : False := by grind
  exact eq538567

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq163 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq170 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | (have r₁ := eq163 X0 X1
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq163 X1 X1
       have r₂ := eq46 X1 X1
       grind)
    | exact resolve eq163 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq163
  have eq1614 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq170
  have eq1642 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq2235 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1642 (σ X1) (σ X0)
       grind)
    | exact superpose eq1642 eq15
    | exact resolve eq15 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2248 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2235 X0 X1
       have i₂ := eq1642 X1 X0
       grind)
    | exact superpose eq1642 eq2235
    | exact resolve eq2235 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642 eq2235
  have eq2260 : False := by grind
  exact eq2260
