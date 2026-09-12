import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
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
  have eq90 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq104
    | (have j0 := eq104 X0
       grind)
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq104
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq115 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1120 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1174 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1120 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1120
    | (have j0 := eq1120 X0 X1
       grind)
    | exact resolve eq1120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1578 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (M.op (τ X0) X1)
       have i₂ := eq22 (τ X0) X1
       grind)
    | exact superpose eq22 eq87
    | (have j0 := eq87 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq87 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1609 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq2102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq314
       have i₂ := eq1174 y x
       grind)
    | exact superpose eq1174 eq314
    | (have j1 := eq1174 (σ x) (σ y)
       grind)
    | (have r₁ := eq314
       have r₂ := eq1174 y x
       grind)
    | (have r₁ := eq314
       have r₂ := eq1174 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq314
       have r₂ := eq1174 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq314 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq2103 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2102
  have eq14510 : ∀ X0 X1 : G, (τ (σ (M.op (τ (σ X0)) X1))) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq1609 (σ X0) X1
       grind)
    | exact superpose eq1609 eq38
    | (have j1 := eq1609 (σ X0) X1
       grind)
    | exact resolve eq38 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq14540 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14510 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq14510
    | (have j0 := eq14510 X0 X1
       grind)
    | exact resolve eq14510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14510
  have eq14572 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14540 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14540
    | (have j0 := eq14540 X0 X1
       grind)
    | exact resolve eq14540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14540
  have eq14588 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14572 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14572
    | (have j0 := eq14572 X0 X1
       grind)
    | exact resolve eq14572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14572
  have eq14597 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14588 X0 X1
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq14588 X0 X1
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq14588 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq14588
  have eq14684 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (M.op (σ X0) X1)
       have i₂ := eq14597 (σ X0) X1
       grind)
    | exact superpose eq14597 eq38
    | exact resolve eq38 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq14597
  have eq84949 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2103
       grind)
    | exact superpose eq2103 eq16
    | exact resolve eq16 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq84950 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq84949
       have r₂ := eq130 x
       grind)
    | exact resolve eq84949 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84949
  have eq85734 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq84950
       grind)
    | exact superpose eq84950 eq10
    | exact resolve eq10 eq84950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84950
  have eq85853 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85734
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85734
    | exact resolve eq85734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85734
  have eq85859 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85853
       grind)
    | exact superpose eq85853 eq16
    | exact resolve eq16 eq85853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85853
  have eq85860 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85859
       have r₂ := eq130 x
       grind)
    | exact resolve eq85859 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85859
  have eq86682 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq85860
       grind)
    | exact superpose eq85860 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq85860
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq85860
       grind)
    | exact resolve eq12 eq85860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86686 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22 x y
       have i₂ := eq85860
       grind)
    | exact superpose eq85860 eq22
    | exact resolve eq22 eq85860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq85860
  have eq86805 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq86682
  have eq86819 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14684 x (σ y)
       have i₂ := eq86686
       grind)
    | exact superpose eq86686 eq14684
    | exact resolve eq14684 eq86686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14684 eq86686
  have eq87010 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86819
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq86819
    | exact resolve eq86819 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86819
  have eq87020 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87010
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq87010
    | exact resolve eq87010 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq87010
  have eq87021 : x = (M.op x x) := by grind
  clear eq87020
  have eq113857 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq325 x y
       have i₂ := eq86805
       grind)
    | exact superpose eq86805 eq325
    | (have j0 := eq325 x y
       grind)
    | exact resolve eq325 eq86805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq86805
  have eq113884 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq113857
  have eq113885 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq113884
  have eq113897 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq113885
       grind)
    | exact superpose eq113885 eq10
    | exact resolve eq10 eq113885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113885
  have eq114024 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq113897
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq113897
    | exact resolve eq113897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113897
  have eq114854 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114024
       grind)
    | exact superpose eq114024 eq16
    | exact resolve eq16 eq114024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114024
  have eq114861 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq114854
       have r₂ := eq130 x
       grind)
    | exact resolve eq114854 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq114854
  have eq114868 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114861
       grind)
    | exact superpose eq114861 eq16
    | exact resolve eq16 eq114861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114895 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq114861
       grind)
    | exact superpose eq114861 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq114861
       grind)
    | exact resolve eq12 eq114861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114861
  have eq115039 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq114895
  have eq115112 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq115039
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq115039
    | exact resolve eq115039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115039
  have eq115991 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1174 y x
       have i₂ := eq115112
       grind)
    | exact superpose eq115112 eq1174
    | (have j0 := eq1174 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1174 eq115112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq115112
  have eq116125 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115991
       have r₂ := eq114868
       grind)
    | exact resolve eq115991 eq114868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115991
  have eq116727 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114868
       have i₂ := eq116125
       grind)
    | exact superpose eq116125 eq114868
    | exact resolve eq114868 eq116125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116125
  have eq116732 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116727
       have i₂ := eq87021
       grind)
    | exact superpose eq87021 eq116727
    | exact resolve eq116727 eq87021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87021 eq116727
  have eq116733 : x = (M.op x y) := by grind
  clear eq116732
  have eq118094 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq114868
       have i₂ := eq116733
       grind)
    | exact superpose eq116733 eq114868
    | exact resolve eq114868 eq116733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114868 eq116733
  have eq118257 : False := by grind
  exact eq118257

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq364 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq378 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq364 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq381 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq377 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq377 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq377 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq397 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq381 (σ X0)
       grind)
    | exact superpose eq381 eq15
    | exact resolve eq15 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq397
    | exact resolve eq397 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq397
  have eq467 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0) (σ X0)
       have i₂ := eq416 X0
       grind)
    | exact superpose eq416 eq71
    | exact resolve eq71 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq467 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq467
    | exact resolve eq467 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq475 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq470 X0
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq470
    | exact resolve eq470 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq470
  have eq519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq378 (σ X0) (σ X1)
       grind)
    | exact superpose eq378 eq15
    | (have j1 := eq378 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq378 (τ X0) X1
       grind)
    | exact superpose eq378 eq18
    | (have j1 := eq378 (τ X0) X1
       grind)
    | exact resolve eq18 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq378
  have eq536 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq416 X1
       grind)
    | exact superpose eq416 eq519
    | (have j0 := eq519 X0 X1
       grind)
    | exact resolve eq519 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq519
  have eq1026 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq527 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq527
    | exact resolve eq527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq1087 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1026
    | (have j0 := eq1026 X0 X1
       grind)
    | exact resolve eq1026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1584 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq16
    | (have j1 := eq536 x y
       grind)
    | exact resolve eq16 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1584
       have i₂ := eq1087 x y
       grind)
    | exact superpose eq1087 eq1584
    | (have j1 := eq1087 x y
       grind)
    | (have r₁ := eq1584
       have r₂ := eq1087 x y
       grind)
    | exact resolve eq1584 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq1584
  have eq1657 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1656
  have eq1665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq475 y
       have i₂ := eq1657
       grind)
    | exact superpose eq1657 eq475
    | exact resolve eq475 eq1657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657
  have eq1684 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1665
       have r₂ := eq16
       grind)
    | exact resolve eq1665 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq1690 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1684
       grind)
    | exact superpose eq1684 eq10
    | exact resolve eq10 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1737 : x = (M.op y y) := by
    first
    | (have i₁ := eq1690
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1690
    | exact resolve eq1690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq475 y
       have i₂ := eq1737
       grind)
    | exact superpose eq1737 eq475
    | exact resolve eq475 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq1737
  have eq1763 : False := by grind
  exact eq1763

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq24 eq35
  have eq76 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq396 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq395
  have eq835 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq396 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq396
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq396
       grind)
    | exact resolve eq13 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq843 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq835
  have eq846 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq843
    | exact resolve eq843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120 eq846
    | exact resolve eq846 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq846
  have eq879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq871
  have eq882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq879
       have r₂ := eq131
       grind)
    | exact resolve eq879 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq879
  have eq883 : x = (M.op x y) := by
    first
    | (have r₁ := eq882
       have r₂ := eq27
       grind)
    | exact resolve eq882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq884 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq883 eq20
    | exact resolve eq20 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq889 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq883 eq76
    | (have r₁ := eq76
       have r₂ := eq883
       grind)
    | exact resolve eq76 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq894 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq889
  have eq901 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq884
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq884
    | exact resolve eq884 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq902 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq901 eq26
    | exact resolve eq26 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1427 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq894
       grind)
    | exact resolve eq13 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1435 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq1427
  have eq1437 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1435
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1435
    | exact resolve eq1435 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1435
  have eq1440 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq883 eq1437
    | exact resolve eq1437 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq1437
  have eq1441 : x = (k x y) := by grind
  clear eq1440
  have eq1445 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq44
    | exact resolve eq44 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1441
  have eq1452 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq901 eq1445
    | exact resolve eq1445 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1454 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1452
    | exact resolve eq1452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1452
  have eq1455 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq901 eq1454
    | exact resolve eq1454 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq1454
  have eq1458 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1455 eq94
    | (have j0 := eq94 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq94 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1455
  have eq1459 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1458
  have eq1461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq902 eq1459
    | exact resolve eq1459 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq1459
  have eq1464 : False := by grind
  exact eq1464

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq17
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq299 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
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
  have eq304 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq304 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq306 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq299 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq307 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq305 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq305 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq305 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq318 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq307 (σ X0)
       grind)
    | exact superpose eq307 eq15
    | exact resolve eq15 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq307 (τ X0)
       grind)
    | exact superpose eq307 eq31
    | exact resolve eq31 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq331 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq324
    | exact resolve eq324 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq337 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq318
    | exact resolve eq318 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq318
  have eq402 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (τ X0) (τ X0)
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq63
    | exact resolve eq63 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq306 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq600 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq612 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq600 X0 (τ X1)
       grind)
    | exact superpose eq600 eq18
    | (have j1 := eq600 X0 (τ X1)
       grind)
    | exact resolve eq18 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq600
  have eq1007 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X1) X0
       have i₂ := eq612 X0 X1
       grind)
    | exact superpose eq612 eq63
    | (have j1 := eq612 (τ X0) X0
       grind)
    | exact resolve eq63 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq612
  have eq1015 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1138 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1015
    | (have j0 := eq1015 (σ X0) X1
       grind)
    | exact resolve eq1015 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1173 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1138
    | (have j0 := eq1138 X0 X1
       grind)
    | exact resolve eq1138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1175 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1173 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1173
    | (have j0 := eq1173 X0 X1
       grind)
    | exact resolve eq1173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1176 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1177 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1176
    | (have j0 := eq1176 X0 X1
       grind)
    | exact resolve eq1176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1186 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0
       have i₂ := eq1177 X0 X1
       grind)
    | exact superpose eq1177 eq402
    | (have j1 := eq1177 (τ X0) X1
       grind)
    | exact resolve eq402 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq1177
  have eq1217 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1306 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 (σ X0))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq337 X0
       grind)
    | exact superpose eq337 eq1217
    | (have j0 := eq1217 (σ X0) X1
       grind)
    | exact resolve eq1217 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq1217
  have eq1338 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 (σ X0))) = (σ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1340 : ∀ X0 X1 : G, (σ (k X1 (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1338
    | (have j0 := eq1338 X0 X1
       grind)
    | exact resolve eq1338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1412 : ∀ X0 X1 : G, (k X0 (σ X1)) = (τ (σ (M.op X0 (σ X1)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (σ X1))
       have i₂ := eq1340 X1 X0
       grind)
    | exact superpose eq1340 eq10
    | (have j1 := eq1340 X1 X1
       grind)
    | exact resolve eq10 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1454 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq10 (M.op X0 (σ X1))
       grind)
    | exact superpose eq10 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1456 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1454 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1454
    | (have j0 := eq1454 X0 (τ X0)
       grind)
    | exact resolve eq1454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1489 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1456 X0 X1
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq1456
    | (have j0 := eq1456 X0 X1
       grind)
    | exact resolve eq1456 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq1456
  have eq1500 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq1489 X0 X1
       grind)
    | exact superpose eq1489 eq11
    | (have j1 := eq1489 X0 X1
       grind)
    | exact resolve eq11 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1518 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1526 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1518 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1518 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1547 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1526 (σ X1) (σ X0)
       grind)
    | exact superpose eq1526 eq15
    | exact resolve eq15 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1574 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 X0 X1
       have i₂ := eq1526 X1 X0
       grind)
    | exact superpose eq1526 eq1547
    | exact resolve eq1547 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526 eq1547
  have eq2079 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1574 x y
       grind)
    | exact superpose eq1574 eq16
    | (have r₁ := eq16
       have r₂ := eq1574 x y
       grind)
    | exact resolve eq16 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq2112 : False := by grind
  exact eq2112

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  clear eq17
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
  clear eq18
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
  have eq428 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3114 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq428
    | exact resolve eq428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq3168 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3114 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3114
    | (have j0 := eq3114 X0 X1
       grind)
    | exact resolve eq3114 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3202 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3168 X1 X0
       grind)
    | exact superpose eq3168 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3168 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3168 X0 X1
       grind)
    | exact resolve eq12 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3249 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3361 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3249 X0 X1
       grind)
    | exact superpose eq3249 eq11
    | (have j1 := eq3249 X0 X1
       grind)
    | exact resolve eq11 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq3476 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3361 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3361
    | (have j0 := eq3361 X0 X1
       grind)
    | exact resolve eq3361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361
  have eq3477 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3476 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3502 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq3477 (σ X0) X1
       grind)
    | exact superpose eq3477 eq22
    | (have j1 := eq3477 X1 (σ X0)
       grind)
    | exact resolve eq22 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3583 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3502 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3502
    | exact resolve eq3502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502
  have eq3667 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3583 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3583
    | (have j0 := eq3583 X0 X1
       grind)
    | exact resolve eq3583 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3583
  have eq3688 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3667 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3667
    | (have j0 := eq3667 (σ X0) (σ X1)
       grind)
    | exact resolve eq3667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq3834 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3688 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3688
    | (have j0 := eq3688 X0 X1
       grind)
    | exact resolve eq3688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3688
  have eq7392 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3834 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq3834 X0 X1
       grind)
    | exact superpose eq3834 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq3834 X1 X0
       grind)
    | exact resolve eq12 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7394 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq3834 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq3834 X0 X1
       grind)
    | exact superpose eq3834 eq13
    | (have j1 := eq3834 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq3834 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq3834 X0 X1
       grind)
    | exact resolve eq13 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq7400 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7394
  have eq7404 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7400 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7400
    | (have j0 := eq7400 X0 X1
       grind)
    | exact resolve eq7400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7400
  have eq7406 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7392 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7392
    | (have j0 := eq7392 X0 X1
       grind)
    | exact resolve eq7392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7414 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7406 X0 X1
       have j1 := eq7404 X0 X1
       grind)
    | (have r₁ := eq7406 X0 X1
       have r₂ := eq7404 X0 X1
       grind)
    | exact resolve eq7406 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404 eq7406
  have eq7477 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7414 x y
       grind)
    | exact superpose eq7414 eq16
    | (have j1 := eq7414 x y
       grind)
    | exact resolve eq16 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414
  have eq7526 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq7477
       have i₂ := eq3477 x y
       grind)
    | exact superpose eq3477 eq7477
    | (have j1 := eq3477 y x
       grind)
    | exact resolve eq7477 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq7533 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7526
  have eq7549 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7533
       grind)
    | exact superpose eq7533 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7551 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7533
       grind)
    | exact superpose eq7533 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq7533
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7533
       grind)
    | exact resolve eq13 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7533
  have eq7557 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7551
  have eq7559 : (M.op x y) = (k y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq7549
       have r₂ := eq7557
       grind)
    | exact resolve eq7549 eq7557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7549 eq7557
  have eq7571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7477
       have i₂ := eq7559
       grind)
    | exact superpose eq7559 eq7477
    | exact resolve eq7477 eq7559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7477 eq7559
  have eq7581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7571
  have eq7582 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq7581
  have eq7593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq7582
       grind)
    | exact superpose eq7582 eq11
    | exact resolve eq11 eq7582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq7662 : False := by grind
  exact eq7662

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq100
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq153 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | exact resolve eq151 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq775 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156 x y
       grind)
    | exact superpose eq156 eq16
    | (have j1 := eq156 x y
       grind)
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1046 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq153 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1093 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1046 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1046
    | (have j0 := eq1046 X0 X1
       grind)
    | exact resolve eq1046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq4064 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq775
       have i₂ := eq1093 x y
       grind)
    | exact superpose eq1093 eq775
    | (have j1 := eq1093 x y
       grind)
    | (have r₁ := eq775
       have r₂ := eq1093 x y
       grind)
    | (have r₁ := eq775
       have r₂ := eq1093 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq775
       have r₂ := eq1093 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq775 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq1093
  have eq4065 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq4064
  have eq4572 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4065
       grind)
    | exact superpose eq4065 eq16
    | exact resolve eq16 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4573 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4572
       have r₂ := eq80 x
       grind)
    | exact resolve eq4572 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4573
       grind)
    | exact superpose eq4573 eq103
    | exact resolve eq103 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4592 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4578
       have r₂ := eq16
       grind)
    | exact resolve eq4578 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4595 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4592
       grind)
    | exact superpose eq4592 eq10
    | exact resolve eq10 eq4592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4592
  have eq4643 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4595
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4595
    | exact resolve eq4595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4595
  have eq4646 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4643
       grind)
    | exact superpose eq4643 eq16
    | exact resolve eq16 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq4647 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4646
       have r₂ := eq80 x
       grind)
    | exact resolve eq4646 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4646
  have eq4655 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4647
       grind)
    | exact superpose eq4647 eq10
    | exact resolve eq10 eq4647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4647
  have eq4703 : x = (M.op y y) := by
    first
    | (have i₁ := eq4655
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4655
    | exact resolve eq4655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655
  have eq4716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4703
       grind)
    | exact superpose eq4703 eq103
    | exact resolve eq103 eq4703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4703
  have eq4730 : False := by grind
  exact eq4730

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq758 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3479 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq116 X0 (M.op (τ X0) X1)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq3484 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479
  have eq3485 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3484 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484
  have eq3605 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3485 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3485
    | exact resolve eq3485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq3661 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3605 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3605
    | (have j0 := eq3605 X0 X1
       grind)
    | exact resolve eq3605 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq3707 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3661 X0 X1
       grind)
    | exact superpose eq3661 eq10
    | (have j1 := eq3661 X0 X1
       grind)
    | exact resolve eq10 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3754 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3707 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3707
    | (have j0 := eq3707 X0 X1
       grind)
    | exact resolve eq3707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq3846 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3754 X0 (σ X1)
       grind)
    | exact superpose eq3754 eq28
    | (have j1 := eq3754 X0 (σ X1)
       grind)
    | exact resolve eq28 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3754
  have eq4144 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq3846 (σ X0) X1
       grind)
    | exact superpose eq3846 eq37
    | (have j1 := eq3846 (σ X0) X1
       grind)
    | exact resolve eq37 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3846
  have eq4210 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4144 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4144
    | (have j0 := eq4144 X0 X1
       grind)
    | exact resolve eq4144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4243 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4210 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4210
    | (have j0 := eq4210 X0 X1
       grind)
    | exact resolve eq4210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210
  have eq4253 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4243
    | (have j0 := eq4243 X0 X1
       grind)
    | exact resolve eq4243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4459 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4253 X0 X1
       grind)
    | exact superpose eq4253 eq11
    | (have j1 := eq4253 X0 X1
       grind)
    | exact resolve eq11 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq5340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4459 x y
       grind)
    | exact superpose eq4459 eq16
    | (have j1 := eq4459 x y
       grind)
    | exact resolve eq16 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq5371 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5340
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5340
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5340
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5340
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5340 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5340
       have i₂ := eq3661 x y
       grind)
    | exact superpose eq3661 eq5340
    | (have j1 := eq3661 x y
       grind)
    | (have r₁ := eq5340
       have r₂ := eq3661 x y
       grind)
    | (have r₁ := eq5340
       have r₂ := eq3661 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5340
       have r₂ := eq3661 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5340 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661 eq5340
  have eq5375 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5372
  have eq5376 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5375
  have eq5377 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5371
  have eq5378 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5377
  have eq5382 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5376
       grind)
    | exact superpose eq5376 eq16
    | exact resolve eq16 eq5376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5376
  have eq5383 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5382
       have r₂ := eq22 x
       grind)
    | exact resolve eq5382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5382
  have eq5389 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq758 x y
       have i₂ := eq5383
       grind)
    | exact superpose eq5383 eq758
    | (have j0 := eq758 x y
       grind)
    | exact resolve eq758 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq5383
  have eq5394 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5389
  have eq5395 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5394
  have eq5399 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5378
       grind)
    | exact superpose eq5378 eq16
    | exact resolve eq16 eq5378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5378
  have eq5400 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5399
       have r₂ := eq22 x
       grind)
    | exact resolve eq5399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5410 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5395
       grind)
    | exact superpose eq5395 eq16
    | exact resolve eq16 eq5395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq5432 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5410
       have i₂ := eq5400
       grind)
    | exact superpose eq5400 eq5410
    | exact resolve eq5410 eq5400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400 eq5410
  have eq5433 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5432
  have eq5434 : (σ x) = (σ y) := by grind
  clear eq5433
  have eq5435 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5434
       grind)
    | exact superpose eq5434 eq16
    | exact resolve eq16 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5436 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5434
       grind)
    | exact superpose eq5434 eq10
    | exact resolve eq10 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434
  have eq5490 : x = y := by
    first
    | (have i₁ := eq5436
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5436
    | exact resolve eq5436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq5491 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5435
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5435
    | exact resolve eq5435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5435
  have eq5492 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5491
       have i₂ := eq5490
       grind)
    | exact superpose eq5490 eq5491
    | exact resolve eq5491 eq5490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490 eq5491
  have eq5493 : False := by grind
  exact eq5493

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq19
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
  have eq462 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  clear eq37
  have eq465 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq3045 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq465
    | exact resolve eq465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq3099 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3045 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3045
    | (have j0 := eq3045 X0 X1
       grind)
    | exact resolve eq3045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045
  have eq3346 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq462 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq462 X0 X1
       grind)
    | exact superpose eq462 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq462 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq462 (σ X1) X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq462 X0 X1
       grind)
    | exact resolve eq13 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3350 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq462 (σ x) y
       grind)
    | exact superpose eq462 eq16
    | (have j1 := eq462 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq462 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3354 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3355 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3358 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3350
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3350
    | exact resolve eq3350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3367 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3358
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3358
    | exact resolve eq3358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3605 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3355
    | exact resolve eq3355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3707 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3605 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3605
    | (have j0 := eq3605 X0 X1
       grind)
    | exact resolve eq3605 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3605
  have eq3735 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3707 X1 X0
       grind)
    | exact superpose eq3707 eq11
    | (have j1 := eq3707 X1 X0
       grind)
    | exact resolve eq11 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq3853 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3735 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3735
    | (have j0 := eq3735 X0 X1
       grind)
    | exact resolve eq3735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq3873 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3853 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3853
    | (have j0 := eq3853 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3922 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3853 X0 (τ X1)
       grind)
    | exact superpose eq3853 eq18
    | (have j1 := eq3853 X0 (τ X1)
       grind)
    | exact resolve eq18 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3853
  have eq4031 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3873 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3873
    | (have j0 := eq3873 X0 X1
       grind)
    | exact resolve eq3873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873
  have eq4166 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3922 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3922
    | exact resolve eq3922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq4231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4166 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4166
    | (have j0 := eq4166 X0 X1
       grind)
    | exact resolve eq4166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq11251 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4031 y x
       grind)
    | exact superpose eq4031 eq16
    | (have j1 := eq4031 y x
       grind)
    | exact resolve eq16 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq11338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11251
       have i₂ := eq3099 y x
       grind)
    | exact superpose eq3099 eq11251
    | (have j1 := eq3099 y x
       grind)
    | (have r₁ := eq11251
       have r₂ := eq3099 y x
       grind)
    | (have r₁ := eq11251
       have r₂ := eq3099 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11251
       have r₂ := eq3099 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11251 eq3099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11251
  have eq11339 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11338
  have eq11468 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11339
       grind)
    | exact superpose eq11339 eq16
    | exact resolve eq16 eq11339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11469 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq11468
       have r₂ := eq22 x
       grind)
    | exact resolve eq11468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq11470 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3367
       have i₂ := eq11469
       grind)
    | exact superpose eq11469 eq3367
    | (have r₁ := eq3367
       have r₂ := eq11469
       grind)
    | exact resolve eq3367 eq11469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11469
  have eq11477 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11470
  have eq11478 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11477
  have eq11479 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq11478
       have r₂ := eq3367
       grind)
    | exact resolve eq11478 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367 eq11478
  have eq11481 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11479
       grind)
    | exact superpose eq11479 eq10
    | exact resolve eq10 eq11479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11479
  have eq11543 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11481
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11481
    | exact resolve eq11481 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11481
  have eq11545 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11543
       grind)
    | exact superpose eq11543 eq16
    | exact resolve eq16 eq11543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11543
  have eq11546 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq11545
       have r₂ := eq22 x
       grind)
    | exact resolve eq11545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11545
  have eq11561 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq11546
       grind)
    | exact superpose eq11546 eq11
    | exact resolve eq11 eq11546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11546
  have eq11655 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11561
       grind)
    | exact superpose eq11561 eq16
    | exact resolve eq16 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq11696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11655
       have i₂ := eq4231 y x
       grind)
    | exact superpose eq4231 eq11655
    | (have j1 := eq4231 y x
       grind)
    | (have r₁ := eq11655
       have r₂ := eq4231 y x
       grind)
    | (have r₁ := eq11655
       have r₂ := eq4231 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11655
       have r₂ := eq4231 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11655 eq4231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4231
  have eq11697 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11655
       have i₂ := eq3099 y x
       grind)
    | exact superpose eq3099 eq11655
    | (have j1 := eq3099 y x
       grind)
    | (have r₁ := eq11655
       have r₂ := eq3099 y x
       grind)
    | (have r₁ := eq11655
       have r₂ := eq3099 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11655
       have r₂ := eq3099 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11655 eq3099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq11698 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11697
  have eq11699 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq11696
  have eq11705 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11655
       have i₂ := eq11698
       grind)
    | exact superpose eq11698 eq11655
    | exact resolve eq11655 eq11698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11698
  have eq11706 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11705
  have eq11707 : (M.op x y) = (M.op x x) := by grind
  clear eq11706
  have eq11722 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq11655
       have i₂ := eq11699
       grind)
    | exact superpose eq11699 eq11655
    | exact resolve eq11655 eq11699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11699
  have eq11723 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq11722
  have eq11724 : (k y x) = (M.op x x) := by grind
  clear eq11723
  have eq11734 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11655
       have i₂ := eq11724
       grind)
    | exact superpose eq11724 eq11655
    | exact resolve eq11655 eq11724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11655 eq11724
  have eq11762 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11734
       have i₂ := eq11707
       grind)
    | exact superpose eq11707 eq11734
    | exact resolve eq11734 eq11707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11707 eq11734
  have eq11763 : False := by grind
  exact eq11763
