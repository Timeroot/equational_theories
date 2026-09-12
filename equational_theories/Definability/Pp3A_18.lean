import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq77 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq799 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq12550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12550
    | exact resolve eq12550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12551
       have r₂ := eq28
       grind)
    | exact resolve eq12551 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12551
  have eq12564 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12562
    | exact resolve eq12562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq12569 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq12576 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12564 eq55
    | exact resolve eq55 eq12564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12564
  have eq12605 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12576
    | exact resolve eq12576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576
  have eq12610 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12605
  have eq13918 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq12610
       grind)
    | exact superpose eq12610 eq104
    | exact resolve eq104 eq12610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq12610
  have eq13941 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13918
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13918
    | exact resolve eq13918 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13918
  have eq14186 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13941 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq13941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq14186
    | exact resolve eq14186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14195 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14194
  have eq14207 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14195
    | exact resolve eq14195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195
  have eq14208 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14207
  have eq14221 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14208 eq55
    | exact resolve eq55 eq14208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14208
  have eq14253 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14221
    | exact resolve eq14221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14221
  have eq14254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14253
  have eq14255 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14254 eq28
    | exact resolve eq28 eq14254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14254
  have eq15332 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12569 eq117
    | exact resolve eq117 eq12569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq12569
  have eq15345 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15332
  have eq15353 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15345
       have r₂ := eq14255
       grind)
    | exact resolve eq15345 eq14255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15345
  have eq15370 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq15353
       grind)
    | exact superpose eq15353 eq55
    | exact resolve eq55 eq15353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15353
  have eq15405 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15370
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15370
    | exact resolve eq15370 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15370
  have eq15502 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15405 eq53
    | exact resolve eq53 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405
  have eq15847 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15502
  have eq18154 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15847 eq77
    | exact resolve eq77 eq15847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15847
  have eq18199 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18154
    | exact resolve eq18154 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18154
  have eq18582 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq18199
       grind)
    | exact superpose eq18199 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq18199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18199
  have eq18596 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18582
  have eq18824 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799 x
       have i₂ := eq18596
       grind)
    | exact superpose eq18596 eq799
    | exact resolve eq799 eq18596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18596
  have eq18892 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq18824
    | exact resolve eq18824 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18824
  have eq18899 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18892
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18892
    | exact resolve eq18892 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18892
  have eq18900 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18899
  have eq18908 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18900 eq21
    | exact resolve eq21 eq18900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18900
  have eq19035 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18908
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18908
    | exact resolve eq18908 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18908
  have eq19138 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19035 eq14255
    | (have r₁ := eq14255
       have r₂ := eq19035
       grind)
    | exact resolve eq14255 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14255
  have eq19158 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19138
  have eq19159 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19158
  have eq19349 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19159 eq53
    | exact resolve eq53 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159
  have eq19630 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19349 eq803
    | exact resolve eq803 eq19349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq19349
  have eq19701 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq19630
    | exact resolve eq19630 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19630
  have eq19708 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19701
    | exact resolve eq19701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19701
  have eq19718 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19708 eq28
    | exact resolve eq28 eq19708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19708
  have eq19756 : x = (M.op x y) := by
    first
    | (have r₁ := eq19718
       have r₂ := eq19035
       grind)
    | exact resolve eq19718 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035 eq19718
  have eq19883 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19756 eq21
    | exact resolve eq21 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq19886 : x = (M.op x x) := by
    first
    | exact superpose eq19756 eq52
    | exact resolve eq52 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20025 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19883
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19883
    | exact resolve eq19883 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19883
  have eq20030 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20025 eq27
    | exact resolve eq27 eq20025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq20201 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq799 x
       have i₂ := eq19886
       grind)
    | exact superpose eq19886 eq799
    | exact resolve eq799 eq19886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq20203 : x = (k x x) := by grind
  clear eq19886
  have eq20265 : y = (M.op x y) := by
    first
    | exact superpose eq52 eq20201
    | exact resolve eq20201 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20201
  have eq20272 : y = (M.op x y) := by
    first
    | (have i₁ := eq20265
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20265
    | exact resolve eq20265 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20265
  have eq20279 : x = y := by
    first
    | exact superpose eq19756 eq20272
    | exact resolve eq20272 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19756 eq20272
  have eq20283 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20279
       grind)
    | exact superpose eq20279 eq25
    | exact resolve eq25 eq20279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20279
  have eq20410 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20283
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20283
    | exact resolve eq20283 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20283
  have eq20464 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20025 eq20410
    | exact resolve eq20410 eq20025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20410
  have eq21310 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20464 eq20030
    | exact resolve eq20030 eq20464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20030 eq20464
  have eq21449 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x x
       have i₂ := eq20203
       grind)
    | exact superpose eq20203 eq664
    | (have j0 := eq664 x x
       grind)
    | exact resolve eq664 eq20203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq20203
  have eq21452 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21449
  have eq21453 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21452
  have eq21465 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21453
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21453
    | exact resolve eq21453 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21453
  have eq21479 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20025 eq21465
    | exact resolve eq21465 eq20025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20025 eq21465
  have eq21621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21310 eq21479
    | exact resolve eq21479 eq21310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310 eq21479
  have eq21622 : False := by grind
  exact eq21622

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  clear eq23
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq70 X1 X2 X0
       grind)
    | exact superpose eq70 eq66
    | exact resolve eq66 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq553 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq557 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq822 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq548 X1 X0
       grind)
    | exact superpose eq548 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq548 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq548 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq548 X1 X1
       grind)
    | exact resolve eq13 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq850 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq824 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq851 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq850 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq850 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq850 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq854 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq851 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq851
    | (have j0 := eq851 X0
       grind)
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq858 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq853
    | (have j0 := eq853 X0 X1
       grind)
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1222 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq854 X0
       grind)
    | exact superpose eq854 eq36
    | (have j1 := eq854 X0
       grind)
    | exact resolve eq36 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq854
  have eq1259 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1222 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1222
    | (have j0 := eq1222 X0
       grind)
    | exact resolve eq1222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1267 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (σ (τ (k X0 X0))) = (σ (k (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1259 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq1259
    | exact resolve eq1259 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1318 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1267 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq1267
    | (have j0 := eq1267 X0
       grind)
    | exact resolve eq1267 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1334 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1318 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1318
    | (have j0 := eq1318 X0
       grind)
    | exact resolve eq1318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1461 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (k X0 X0) (σ X1)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X0) X1
       have i₂ := eq1334 X0
       grind)
    | exact superpose eq1334 eq18
    | (have j1 := eq1334 X0
       grind)
    | exact resolve eq18 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1466 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 (σ X1)) = (k (k X0 X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1461 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1461
    | (have j0 := eq1461 X0 X1
       grind)
    | exact resolve eq1461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq5337 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq557
    | exact resolve eq557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq5434 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5337 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5337
    | (have j0 := eq5337 X0 X1
       grind)
    | exact resolve eq5337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5337
  have eq15530 : ∀ X0 : G, (k (σ X0) (σ X0)) ≠ (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ X0)) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1466 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq15531 : ∀ X0 : G, (k (σ X0) (σ X0)) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq15530 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15530
  have eq15533 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15531 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq15531
    | exact resolve eq15531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15531
  have eq15574 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15533 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15533
    | exact resolve eq15533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15533
  have eq15614 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq15574 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq15574
    | exact resolve eq15574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15574
  have eq36907 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq37157 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36907 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq36907
    | (have j0 := eq36907 X0 X1
       grind)
    | exact resolve eq36907 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36907
  have eq37240 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X0
       have i₂ := eq37157 X0 X1
       grind)
    | exact superpose eq37157 eq68
    | (have j1 := eq37157 X0 X0
       grind)
    | exact resolve eq68 eq37157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37391 : ∀ X0 : G, X0 ≠ X0 ∨ (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq37157 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37157
  have eq37392 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq37391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37391
  have eq37539 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq37392 X0
       grind)
    | exact superpose eq37392 eq11
    | (have j1 := eq37392 X0
       grind)
    | exact resolve eq11 eq37392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37392
  have eq37685 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37539 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq37539
    | (have j0 := eq37539 X0
       grind)
    | exact resolve eq37539 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37539
  have eq37719 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq37685
  have eq37830 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37719 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq37719
    | exact resolve eq37719 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37719
  have eq45151 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq858 (τ X1) (τ X0)
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq858
    | (have j0 := eq858 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq858 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45244 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq858 (k X0 X0) X0
       have i₂ := eq15614 X0
       grind)
    | exact superpose eq15614 eq858
    | (have j0 := eq858 X0 X0
       grind)
    | exact resolve eq858 eq15614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq15614
  have eq45262 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq45244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45244
  have eq45352 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq45262 X0
       have j1 := eq37830 X0
       grind)
    | (have r₁ := eq45262 X0
       have r₂ := eq37830 X0
       grind)
    | exact resolve eq45262 eq37830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37830 eq45262
  have eq45421 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45151 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45151
    | (have j0 := eq45151 X0 X1
       grind)
    | exact resolve eq45151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45151
  have eq45474 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45421 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45421
    | (have j0 := eq45421 X0 X1
       grind)
    | exact resolve eq45421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45421
  have eq45527 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X1) (τ X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45474 X0 X1
       have i₂ := eq45352 (τ X1)
       grind)
    | exact superpose eq45352 eq45474
    | (have j0 := eq45474 X0 X1
       grind)
    | exact resolve eq45474 eq45352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45474
  have eq45579 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X1)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45527 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq45527
    | (have j0 := eq45527 X0 X1
       grind)
    | exact resolve eq45527 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45527
  have eq45627 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45579 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45579
    | (have j0 := eq45579 X0 X1
       grind)
    | exact resolve eq45579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45579
  have eq45669 : ∀ X0 X1 : G, (k X0 X1) = (k X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq45627 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45627
    | (have j0 := eq45627 X0 X1
       grind)
    | exact resolve eq45627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45627
  have eq45711 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k (τ X1) (τ X1))) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45669 X0 X1
       have i₂ := eq45352 (τ X1)
       grind)
    | exact superpose eq45352 eq45669
    | (have j0 := eq45669 X0 X1
       grind)
    | exact resolve eq45669 eq45352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45669
  have eq45747 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X1) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45711 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq45711
    | (have j0 := eq45711 X0 X1
       grind)
    | exact resolve eq45711 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45711
  have eq45776 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X1) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45747 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45747
    | (have j0 := eq45747 X0 X1
       grind)
    | exact resolve eq45747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45747
  have eq45805 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (k X1 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45776 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45776
    | (have j0 := eq45776 X0 X1
       grind)
    | exact resolve eq45776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45776
  have eq45849 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45352 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45352
    | exact resolve eq45352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45966 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq45352 X0
       grind)
    | exact superpose eq45352 eq66
    | exact resolve eq66 eq45352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46091 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq45849 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq45849
    | exact resolve eq45849 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq45849
  have eq46149 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46091 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46091
    | exact resolve eq46091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46091
  have eq46477 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq46149 (τ X0)
       grind)
    | exact superpose eq46149 eq33
    | exact resolve eq33 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq46553 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46477 X0
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq46477
    | exact resolve eq46477 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46477
  have eq46773 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq45966 X0
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq45966
    | exact resolve eq45966 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45966
  have eq47353 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (τ X0) (τ X0) X1
       have i₂ := eq46553 X0
       grind)
    | exact superpose eq46553 eq70
    | exact resolve eq70 eq46553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46553
  have eq47710 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq46773 X0
       grind)
    | exact superpose eq46773 eq66
    | exact resolve eq66 eq46773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47713 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq46773 X0
       grind)
    | exact superpose eq46773 eq70
    | exact resolve eq70 eq46773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46773
  have eq124617 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq37240 X0 X1
       grind)
    | exact superpose eq37240 eq11
    | (have j1 := eq37240 X0 X0
       grind)
    | exact resolve eq11 eq37240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37240
  have eq124899 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq124617 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq124617
    | (have j0 := eq124617 X0 X0
       grind)
    | exact resolve eq124617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124617
  have eq125307 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47353 X0 X1
       have i₂ := eq124899 X0 X2
       grind)
    | exact superpose eq124899 eq47353
    | (have j1 := eq124899 X0 X2
       grind)
    | exact resolve eq47353 eq124899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47353
  have eq125353 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X0 X1
       have i₂ := eq124899 X0 X2
       grind)
    | exact superpose eq124899 eq70
    | (have j1 := eq124899 X0 X2
       grind)
    | exact resolve eq70 eq124899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq125358 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X0 X0
       have i₂ := eq124899 X0 X1
       grind)
    | exact superpose eq124899 eq88
    | (have j1 := eq124899 X0 X2
       grind)
    | exact resolve eq88 eq124899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq124899
  have eq125601 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125358 X0 X1 X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq125358
    | (have j0 := eq125358 X0 X1 X2
       grind)
    | exact resolve eq125358 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125358
  have eq125604 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125353 X0 X1 X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq125353
    | (have j0 := eq125353 X0 X1 X2
       grind)
    | exact resolve eq125353 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125353
  have eq125633 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = X1 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125307 X0 X1 X2
       have i₂ := eq66 (τ X0) X1
       grind)
    | exact superpose eq66 eq125307
    | (have j0 := eq125307 X0 X1 X2
       grind)
    | exact resolve eq125307 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125307
  have eq126134 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq125601 X0 X2 (τ X1)
       grind)
    | exact superpose eq125601 eq18
    | (have j1 := eq125601 X0 X2 (τ X1)
       grind)
    | exact resolve eq18 eq125601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq125601
  have eq128832 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X0) = X1 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45805 X2 X0
       have i₂ := eq125604 X0 X1 X2
       grind)
    | exact superpose eq125604 eq45805
    | (have j0 := eq45805 (M.op X0 X1) X0
       have j1 := eq125604 X0 X2 X1
       grind)
    | (have r₁ := eq45805 X0 (M.op X0 X0)
       have r₂ := eq125604 X0 X1 (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq45805 eq125604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45805 eq125604
  have eq129268 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X0) = X1 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128832 X0 X1 X2
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq128832
    | (have j0 := eq128832 X0 X1 X2
       grind)
    | exact resolve eq128832 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128832
  have eq129396 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129268 X0 X1 X2
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq129268
    | (have j0 := eq129268 X0 X1 X2
       grind)
    | exact resolve eq129268 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129268
  have eq129397 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq129396 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129396
  have eq130362 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125633 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125633
    | (have j0 := eq125633 (σ X0) X1 X2
       grind)
    | exact resolve eq125633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130540 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (τ X1) X0
       have i₂ := eq125633 X1 X0 X2
       grind)
    | exact superpose eq125633 eq66
    | (have j1 := eq125633 X1 X1 X2
       grind)
    | exact resolve eq66 eq125633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125633
  have eq130675 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = X2 ∨ (M.op X0 X1) = X1 ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130362 X0 X1 X2
       have i₂ := eq45352 X0
       grind)
    | exact superpose eq45352 eq130362
    | (have j0 := eq130362 X0 X1 X2
       grind)
    | exact resolve eq130362 eq45352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130362
  have eq130743 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (k X2 (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (σ (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130675 X0 X1 X2
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq130675
    | (have j0 := eq130675 X0 X1 X2
       grind)
    | exact resolve eq130675 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130675
  have eq169421 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X2 (τ (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq130540 X2 (σ X0) (σ X1)
       grind)
    | exact superpose eq130540 eq15
    | (have j1 := eq130540 X2 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq130540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130540
  have eq169801 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169421 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169421
    | (have j0 := eq169421 X0 X1 X2
       grind)
    | exact resolve eq169421 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169421
  have eq169952 : ∀ X0 X1 X2 : G, (σ X1) = (σ (k X0 X0)) ∨ (M.op X2 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169801 X0 X1 X2
       have i₂ := eq45352 X0
       grind)
    | exact superpose eq45352 eq169801
    | (have j0 := eq169801 X0 X1 X2
       grind)
    | exact resolve eq169801 eq45352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45352 eq169801
  have eq170069 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169952 X0 X1 X2
       have i₂ := eq46149 X0
       grind)
    | exact superpose eq46149 eq169952
    | (have j0 := eq169952 X0 X1 X2
       grind)
    | exact resolve eq169952 eq46149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46149 eq169952
  have eq209122 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X2) = X2 ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq130743 X0 X2 (σ X1)
       grind)
    | exact superpose eq130743 eq15
    | (have j1 := eq130743 X0 X2 (σ X1)
       grind)
    | exact resolve eq15 eq130743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130743
  have eq231978 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126134 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126134
    | (have j0 := eq126134 X1 X1 X2
       grind)
    | exact resolve eq126134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126134
  have eq232813 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231978 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq231978
    | (have j0 := eq231978 X0 X1 X2
       grind)
    | exact resolve eq231978 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231978
  have eq460190 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129397 (M.op X0 X1) X0 X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq129397
    | (have j0 := eq129397 (M.op X0 X1) X0 X2
       grind)
    | exact resolve eq129397 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129397
  have eq460759 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq460190 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460190
  have eq661430 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op X0 x) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq170069 x y X0
       grind)
    | exact superpose eq170069 eq16
    | (have j1 := eq170069 x y X0
       grind)
    | exact resolve eq16 eq170069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170069
  have eq664084 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op X0 x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op X1 x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq661430 X0
       have i₂ := eq232813 y x X1
       grind)
    | exact superpose eq232813 eq661430
    | (have j0 := eq661430 X0
       have j1 := eq232813 y x X0
       grind)
    | (have r₁ := eq661430 X0
       have r₂ := eq232813 y x x
       grind)
    | exact resolve eq661430 eq232813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232813 eq661430
  have eq664087 : ∀ X0 X1 : G, y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op X1 x) ∨ x = (M.op X0 x) := by
    intro X0 X1
    first
    | (have j0 := eq664084 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664084
  have eq669075 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq209122 x y X0
       grind)
    | exact superpose eq209122 eq16
    | (have j1 := eq209122 x y X0
       grind)
    | exact resolve eq16 eq209122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209122
  have eq674075 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq669075 X0
       have i₂ := eq5434 y x
       grind)
    | exact superpose eq5434 eq669075
    | (have j0 := eq669075 X0
       have j1 := eq5434 y x
       grind)
    | (have r₁ := eq669075 X0
       have r₂ := eq5434 y x
       grind)
    | exact resolve eq669075 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434 eq669075
  have eq674076 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq674075 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674075
  have eq706955 : ∀ X0 X1 : G, x = (M.op y x) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq66 x x
       have i₂ := eq664087 X1 X0
       grind)
    | exact superpose eq664087 eq66
    | (have j1 := eq664087 y y
       grind)
    | exact resolve eq66 eq664087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664087
  have eq762778 : ∀ X0 : G, x ≠ x ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op X0 x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq706955 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706955
  have eq762779 : ∀ X0 : G, x = (M.op y x) ∨ x = (M.op X0 x) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq762778 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762778
  have eq762930 : x ≠ x ∨ x = (M.op y x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have j0 := eq762779 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762779
  have eq762931 : x = (M.op y x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq762930
  have eq762946 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq762931
       grind)
    | exact superpose eq762931 eq66
    | exact resolve eq66 eq762931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763071 : ∀ X0 : G, x ≠ y ∨ y = (M.op x x) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq460759 y x x
       have i₂ := eq762931
       grind)
    | exact superpose eq762931 eq460759
    | exact resolve eq460759 eq762931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460759 eq762931
  have eq763098 : ∀ X0 : G, x = y ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x X0) = X0 ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq674076 X0
       have i₂ := eq762946
       grind)
    | exact superpose eq762946 eq674076
    | (have j0 := eq674076 X0
       grind)
    | exact resolve eq674076 eq762946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674076
  have eq763241 : ∀ X0 : G, x = y ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq763098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763098
  have eq763255 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq763241 X0
       have j1 := eq763071 X0
       grind)
    | (have r₁ := eq763241 X0
       have r₂ := eq763071 X0
       grind)
    | exact resolve eq763241 eq763071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763071 eq763241
  have eq764135 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq47710 x
       have i₂ := eq763255 X0
       grind)
    | exact superpose eq763255 eq47710
    | (have j1 := eq763255 X0
       grind)
    | exact resolve eq47710 eq763255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763255
  have eq780441 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq764135 X0
       grind)
    | exact superpose eq764135 eq16
    | (have j1 := eq764135 X0
       grind)
    | exact resolve eq16 eq764135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764135
  have eq780747 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq780441 X0
       have i₂ := eq762946
       grind)
    | exact superpose eq762946 eq780441
    | (have j0 := eq780441 X0
       grind)
    | exact resolve eq780441 eq762946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762946 eq780441
  have eq780773 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq780747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780747
  have eq780774 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq780773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780773
  have eq780853 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47710 x
       have i₂ := eq780774 X0
       grind)
    | exact superpose eq780774 eq47710
    | (have j1 := eq780774 X0
       grind)
    | exact resolve eq47710 eq780774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47710
  have eq780922 : ∀ X0 : G, (τ (σ y)) = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq780774 X0
       grind)
    | exact superpose eq780774 eq10
    | (have j1 := eq780774 X0
       grind)
    | exact resolve eq10 eq780774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780774
  have eq781392 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq780922 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq780922
    | (have j0 := eq780922 X0
       grind)
    | exact resolve eq780922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780922
  have eq781822 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x x
       have i₂ := eq781392 X0
       grind)
    | exact superpose eq781392 eq68
    | (have j1 := eq781392 y
       grind)
    | exact resolve eq68 eq781392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq781392
  have eq782438 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq781822 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781822
  have eq782439 : y = (M.op x y) := by grind
  clear eq782438
  have eq786458 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq780853 X0
       grind)
    | exact superpose eq780853 eq16
    | (have j1 := eq780853 X0
       grind)
    | exact resolve eq16 eq780853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780853
  have eq786724 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq786458 X0
       have i₂ := eq782439
       grind)
    | exact superpose eq782439 eq786458
    | (have j0 := eq786458 X0
       grind)
    | exact resolve eq786458 eq782439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786458
  have eq786725 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq786724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786724
  have eq786877 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47713 x X0
       have i₂ := eq786725 x
       grind)
    | exact superpose eq786725 eq47713
    | exact resolve eq47713 eq786725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47713 eq786725
  have eq787294 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq786877 X0
       have i₂ := eq66 (σ x) X0
       grind)
    | exact superpose eq66 eq786877
    | exact resolve eq786877 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq786877
  have eq788573 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq787294 (σ y)
       grind)
    | exact superpose eq787294 eq16
    | exact resolve eq16 eq787294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787294
  have eq789149 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq788573
       have i₂ := eq782439
       grind)
    | exact superpose eq782439 eq788573
    | exact resolve eq788573 eq782439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782439 eq788573
  have eq789150 : False := by grind
  exact eq789150

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq462 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq463 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq468 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq463 X0 X1
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq463 X1 X1
       have r₂ := eq116 X1 X1
       grind)
    | exact resolve eq463 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq463
  have eq637 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq468 (σ X1) (σ X0)
       grind)
    | exact superpose eq468 eq15
    | exact resolve eq15 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq468 X1 X0
       grind)
    | exact superpose eq468 eq637
    | exact resolve eq637 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq637
  have eq647 : False := by grind
  exact eq647

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (τ X0) (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq110
    | exact resolve eq110 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq150 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq9
    | exact resolve eq9 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq116 X1 X2 X0
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) = (M.op X0 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) X0
       have i₂ := eq134 X1 X0
       grind)
    | exact superpose eq134 eq110
    | exact resolve eq110 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq409 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq410 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq547 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq410 x y
       grind)
    | exact superpose eq410 eq16
    | (have j1 := eq410 x y
       grind)
    | exact resolve eq16 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq21069 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq21194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21069 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq21069
    | (have j0 := eq21069 X0 X1
       grind)
    | exact resolve eq21069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21069
  have eq35245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq547
       have i₂ := eq21194 x y
       grind)
    | exact superpose eq21194 eq547
    | (have j1 := eq21194 (σ x) (σ y)
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 x y
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq547 eq21194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq21194
  have eq35246 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq35245
  have eq336913 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35246
       grind)
    | exact superpose eq35246 eq16
    | exact resolve eq16 eq35246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35246
  have eq336914 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq336913
       have r₂ := eq22 x
       grind)
    | exact resolve eq336913 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336913
  have eq336921 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq336914
       grind)
    | exact superpose eq336914 eq114
    | exact resolve eq114 eq336914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq336914
  have eq337057 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq336921
       grind)
    | exact superpose eq336921 eq10
    | exact resolve eq10 eq336921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336921
  have eq337207 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq337057
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq337057
    | exact resolve eq337057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337057
  have eq337209 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337207
       grind)
    | exact superpose eq337207 eq16
    | exact resolve eq16 eq337207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337207
  have eq337210 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq337209
       have r₂ := eq22 x
       grind)
    | exact resolve eq337209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq337209
  have eq337240 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq337210
       grind)
    | exact superpose eq337210 eq116
    | exact resolve eq116 eq337210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq337210
  have eq337367 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq337240 X0
       have i₂ := eq110 (σ y) X0
       grind)
    | exact superpose eq110 eq337240
    | exact resolve eq337240 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337240
  have eq337921 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq337367 X0
       grind)
    | exact superpose eq337367 eq176
    | (have j1 := eq337367 X1
       grind)
    | exact resolve eq176 eq337367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337367
  have eq338001 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq337921 X1 X1
       have i₂ := eq110 y X1
       grind)
    | exact superpose eq110 eq337921
    | (have j0 := eq337921 X0 X1
       grind)
    | exact resolve eq337921 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337921
  have eq338539 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ y)) X0) (τ (σ y))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (σ y) X0
       have i₂ := eq338001 X1 (σ y)
       grind)
    | exact superpose eq338001 eq150
    | (have j1 := eq338001 X1 X1
       grind)
    | exact resolve eq150 eq338001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq338001
  have eq339542 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq338539 X0 X1
       have i₂ := eq110 (τ (σ y)) X0
       grind)
    | exact superpose eq110 eq338539
    | (have j0 := eq338539 X0 X1
       grind)
    | exact resolve eq338539 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338539
  have eq339874 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq339542 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339542
    | (have j0 := eq339542 X0 X1
       grind)
    | exact resolve eq339542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339542
  have eq341047 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq339874 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339874
  have eq341048 : y = (M.op y y) := by grind
  clear eq341047
  have eq341195 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq277 X0 y
       have i₂ := eq341048
       grind)
    | exact superpose eq341048 eq277
    | exact resolve eq277 eq341048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq341694 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq341048
       grind)
    | exact superpose eq341048 eq176
    | exact resolve eq176 eq341048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq341048
  have eq341774 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq341694 x
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq341694
    | exact resolve eq341694 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341694
  have eq342230 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq341195 x
       have i₂ := eq110 (σ y) x
       grind)
    | exact superpose eq110 eq341195
    | exact resolve eq341195 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq341195
  have eq348964 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq342230 (σ x)
       grind)
    | exact superpose eq342230 eq16
    | exact resolve eq16 eq342230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342230
  have eq349070 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq348964
       have i₂ := eq341774 x
       grind)
    | exact superpose eq341774 eq348964
    | exact resolve eq348964 eq341774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341774 eq348964
  have eq349071 : False := by grind
  exact eq349071

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq110 (τ X0) (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq110
    | exact resolve eq110 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq150 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq9
    | exact resolve eq9 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq116 X1 X2 X0
       grind)
    | exact superpose eq116 eq110
    | exact resolve eq110 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) = (M.op X0 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (M.op (M.op (σ X1) X0) (σ (M.op X1 X1))) X0
       have i₂ := eq134 X1 X0
       grind)
    | exact superpose eq134 eq110
    | exact resolve eq110 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq409 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq410 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq547 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq410 x y
       grind)
    | exact superpose eq410 eq16
    | (have j1 := eq410 x y
       grind)
    | exact resolve eq16 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq21069 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq409 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq21194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21069 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq21069
    | (have j0 := eq21069 X0 X1
       grind)
    | exact resolve eq21069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21069
  have eq35245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq547
       have i₂ := eq21194 x y
       grind)
    | exact superpose eq21194 eq547
    | (have j1 := eq21194 (σ x) (σ y)
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 x y
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq547
       have r₂ := eq21194 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq547 eq21194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq21194
  have eq35246 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq35245
  have eq336962 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35246
       grind)
    | exact superpose eq35246 eq16
    | exact resolve eq16 eq35246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35246
  have eq336963 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq336962
       have r₂ := eq22 x
       grind)
    | exact resolve eq336962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336962
  have eq336970 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq336963
       grind)
    | exact superpose eq336963 eq114
    | exact resolve eq114 eq336963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq336963
  have eq337106 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq336970
       grind)
    | exact superpose eq336970 eq10
    | exact resolve eq10 eq336970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336970
  have eq337256 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq337106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq337106
    | exact resolve eq337106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337106
  have eq337258 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337256
       grind)
    | exact superpose eq337256 eq16
    | exact resolve eq16 eq337256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337256
  have eq337259 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq337258
       have r₂ := eq22 x
       grind)
    | exact resolve eq337258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq337258
  have eq337289 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq337259
       grind)
    | exact superpose eq337259 eq116
    | exact resolve eq116 eq337259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq337259
  have eq337416 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq337289 X0
       have i₂ := eq110 (σ y) X0
       grind)
    | exact superpose eq110 eq337289
    | exact resolve eq337289 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337289
  have eq337970 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq337416 X0
       grind)
    | exact superpose eq337416 eq176
    | (have j1 := eq337416 X1
       grind)
    | exact resolve eq176 eq337416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337416
  have eq338050 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq337970 X1 X1
       have i₂ := eq110 y X1
       grind)
    | exact superpose eq110 eq337970
    | (have j0 := eq337970 X0 X1
       grind)
    | exact resolve eq337970 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337970
  have eq338588 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ y)) X0) (τ (σ y))) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (σ y) X0
       have i₂ := eq338050 X1 (σ y)
       grind)
    | exact superpose eq338050 eq150
    | (have j1 := eq338050 X1 X1
       grind)
    | exact resolve eq150 eq338050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq338050
  have eq339591 : ∀ X0 X1 : G, (M.op (τ (σ y)) X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq338588 X0 X1
       have i₂ := eq110 (τ (σ y)) X0
       grind)
    | exact superpose eq110 eq338588
    | (have j0 := eq338588 X0 X1
       grind)
    | exact resolve eq338588 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338588
  have eq339923 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq339591 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339591
    | (have j0 := eq339591 X0 X1
       grind)
    | exact resolve eq339591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339591
  have eq341096 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq339923 y y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339923
  have eq341097 : y = (M.op y y) := by grind
  clear eq341096
  have eq341244 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq277 X0 y
       have i₂ := eq341097
       grind)
    | exact superpose eq341097 eq277
    | exact resolve eq277 eq341097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq341743 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0 y y
       have i₂ := eq341097
       grind)
    | exact superpose eq341097 eq176
    | exact resolve eq176 eq341097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq341097
  have eq341823 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq341743 x
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq341743
    | exact resolve eq341743 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341743
  have eq342279 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq341244 x
       have i₂ := eq110 (σ y) x
       grind)
    | exact superpose eq110 eq341244
    | exact resolve eq341244 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq341244
  have eq349013 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq342279 (σ x)
       grind)
    | exact superpose eq342279 eq16
    | exact resolve eq16 eq342279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342279
  have eq349119 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq349013
       have i₂ := eq341823 x
       grind)
    | exact superpose eq341823 eq349013
    | exact resolve eq349013 eq341823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341823 eq349013
  have eq349120 : False := by grind
  exact eq349120

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyy_pxy_x_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq100
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq100
    | exact resolve eq100 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq125
    | exact resolve eq125 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
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
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq113 sF1
       grind)
    | exact superpose eq113 eq136
    | exact resolve eq136 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq137
    | exact resolve eq137 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq137
  have eq294 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X2) = X2 := by
    intro X1 X2
    first
    | (have j0 := eq297 x X1 X2
       grind)
    | (have r₁ := eq297 x X1 X1
       have r₂ := eq55 x X1
       grind)
    | exact resolve eq297 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq297
  have eq372 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq140
       have i₂ := eq294 sF0 x
       grind)
    | (have i₁ := eq140
       have i₂ := eq294 X0 sF0
       grind)
    | exact superpose eq294 eq140
    | exact resolve eq140 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq372
    | exact resolve eq372 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq372
  have eq3754 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq308 x y
       grind)
    | exact superpose eq308 eq44
    | (have j1 := eq308 x y
       grind)
    | exact resolve eq44 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq3773 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3754
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3754
    | exact resolve eq3754 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq3775 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3773
    | exact resolve eq3773 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3773
  have eq3782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3775 eq308
    | (have j0 := eq308 x (σ y)
       grind)
    | exact resolve eq308 eq3775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq3775
  have eq3791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq3782
    | exact resolve eq3782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3802 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq3791
       have r₂ := eq27
       grind)
    | exact resolve eq3791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3812 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3802 eq126
    | exact resolve eq126 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq3802
  have eq3846 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq3812
    | exact resolve eq3812 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3812
  have eq3847 : y = (M.op y y) := by grind
  clear eq3846
  have eq3850 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3847
       have i₂ := eq294 y X0
       grind)
    | (have i₁ := eq3847
       have i₂ := eq294 X0 y
       grind)
    | exact superpose eq294 eq3847
    | exact resolve eq3847 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq3847
  have eq3994 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq3850 (M.op x x)
       grind)
    | exact superpose eq3850 eq14
    | exact resolve eq14 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4014 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq435 sF0
       have i₂ := eq3850 sF0
       grind)
    | exact superpose eq3850 eq435
    | exact resolve eq435 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq4025 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq3850 sF0
       grind)
    | exact superpose eq3850 eq140
    | exact resolve eq140 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq4039 : y = (σ y) := by
    first
    | (have i₁ := eq4025
       have i₂ := eq3850 sF1
       grind)
    | exact superpose eq3850 eq4025
    | exact resolve eq4025 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4025
  have eq4048 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4014
       have i₂ := eq3850 sF1
       grind)
    | exact superpose eq3850 eq4014
    | exact resolve eq4014 eq3850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3850 eq4014
  have eq4096 : y = (σ y) := by
    first
    | (have i₁ := eq4039
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4039
    | exact resolve eq4039 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4039
  have eq4101 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4048
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4048
    | exact resolve eq4048 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4048
  have eq4107 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq4101
    | exact resolve eq4101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4101
  have eq4137 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq4096 eq26
    | exact resolve eq26 eq4096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4096
  have eq4420 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4137
       have i₂ := eq3994 sF2
       grind)
    | exact superpose eq3994 eq4137
    | exact resolve eq4137 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994 eq4137
  have eq4422 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4420 eq27
    | exact resolve eq27 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4420
  have eq4431 : False := by grind
  exact eq4431

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation3292 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X4 (M.op X3 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op X2 X3)
       have i₂ := eq14 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq98
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq102
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq124
  have eq128 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq127
  have eq134 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq16
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq219 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq246 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq235 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq235
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq247 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq246
  have eq476 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq58 X1 x X3
       have i₂ := eq58 X1 x X0
       grind)
    | (have i₁ := eq58 X0 X0 x
       have i₂ := eq58 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq630 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op (σ x) (σ y)))))) = (M.op (σ x) (M.op X3 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq219 eq630
    | exact resolve eq630 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq689 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op (σ x) (σ y)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq667
    | exact resolve eq667 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq743 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq134 eq247
    | exact resolve eq247 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq768 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | exact superpose eq219 eq743
    | exact resolve eq743 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq743
  have eq769 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq768
       have i₂ := eq216 (M.op y y)
       grind)
    | exact superpose eq216 eq768
    | exact resolve eq768 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq768
  have eq770 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq128 eq769
    | exact resolve eq769 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq786 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq59
    | exact resolve eq59 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 X2 X3 X3 X4
       have i₂ := eq53 X3 X2 (M.op X2 (M.op X3 X4)) X0 X1
       grind)
    | (have i₁ := eq59 X2 X3 X3 X4
       have i₂ := eq53 X0 X1 (M.op X2 (M.op X3 X4)) X3 X2
       grind)
    | exact superpose eq53 eq59
    | exact resolve eq59 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq59
  have eq1290 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq55 sF4
       have i₂ := eq476 sF2 sF4 x
       grind)
    | (have i₁ := eq55 sF4
       have i₂ := eq476 X0 sF4 sF2
       grind)
    | exact superpose eq476 eq55
    | exact resolve eq55 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq476
  have eq1295 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq770 eq1290
    | exact resolve eq1290 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq1290
  have eq12188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq12188
    | exact resolve eq12188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12188
  have eq12200 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq12189
       have r₂ := eq28
       grind)
    | exact resolve eq12189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12189
  have eq12204 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq12200
    | exact resolve eq12200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12200
  have eq12209 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12204 eq90
    | (have r₁ := eq90
       have r₂ := eq12204
       grind)
    | exact resolve eq90 eq12204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq12242 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op (σ x) (σ y)))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq12204 eq820
    | exact resolve eq820 eq12204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq12204
  have eq12244 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq12209
  have eq12245 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq12244
  have eq12247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq689 eq12242
    | exact resolve eq12242 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq12242
  have eq13177 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12245 eq63
    | exact resolve eq63 eq12245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq13178 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12245 eq80
    | exact resolve eq80 eq12245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq12245
  have eq13187 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13178
  have eq13197 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq134 eq13177
    | exact resolve eq13177 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq13177
  have eq13199 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13197
       have r₂ := eq89
       grind)
    | exact resolve eq13197 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq13197
  have eq13202 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13199
       grind)
    | exact superpose eq13199 eq49
    | exact resolve eq49 eq13199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13199
  have eq13219 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13202
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq13202
    | exact resolve eq13202 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq13202
  have eq13235 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13219 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13219
  have eq13236 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13235
  have eq13240 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13236
    | exact resolve eq13236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13249 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13240
    | exact resolve eq13240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13240
  have eq13261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13187 eq12247
    | exact resolve eq12247 eq13187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12247 eq13187
  have eq13291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq13261
  have eq13307 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13291
       have r₂ := eq28
       grind)
    | exact resolve eq13291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13291
  have eq14291 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq13307
       grind)
    | exact superpose eq13307 eq52
    | exact resolve eq52 eq13307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq14310 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (M.op X0 (σ (M.op x y)))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq786 x X1 x
       have i₂ := eq13307
       grind)
    | exact superpose eq13307 eq786
    | exact resolve eq786 eq13307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq13307
  have eq14349 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14310 x x
       have i₂ := eq14 (σ sF0) x x
       grind)
    | exact superpose eq14 eq14310
    | exact resolve eq14310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14310
  have eq14362 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq14291
    | exact resolve eq14291 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14291
  have eq14370 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14349
       have i₂ := eq45 sF0
       grind)
    | exact superpose eq45 eq14349
    | exact resolve eq14349 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq14349
  have eq14376 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq128 eq14370
    | exact resolve eq14370 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq14370
  have eq14377 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1295 eq14376
    | exact resolve eq14376 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq14376
  have eq14378 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq14377
    | exact resolve eq14377 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377
  have eq30286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13249 eq14378
    | exact resolve eq14378 eq13249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13249 eq14378
  have eq30349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq30286
  have eq30384 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq30349
       have r₂ := eq28
       grind)
    | exact resolve eq30349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30349
  have eq32471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30384 eq14362
    | exact resolve eq14362 eq30384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14362 eq30384
  have eq32527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32471
  have eq32570 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq32527
       have r₂ := eq28
       grind)
    | exact resolve eq32527 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32527
  have eq32603 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32570 eq30
    | exact resolve eq30 eq32570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32570
  have eq32711 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32603
    | exact resolve eq32603 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32603
  have eq32712 : x = y := by grind
  clear eq32711
  have eq32729 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32712
       grind)
    | exact superpose eq32712 eq19
    | exact resolve eq19 eq32712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32730 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32712
       grind)
    | exact superpose eq32712 eq25
    | exact resolve eq25 eq32712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32712
  have eq32835 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32730
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32730
    | exact resolve eq32730 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32730
  have eq32850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32835 eq27
    | exact resolve eq27 eq32835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32835
  have eq33138 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32850 eq71
    | exact resolve eq71 eq32850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq32850
  have eq33242 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33138
       have i₂ := eq32729
       grind)
    | exact superpose eq32729 eq33138
    | exact resolve eq33138 eq32729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32729 eq33138
  have eq33297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33242 eq15
    | exact resolve eq15 eq33242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33242
  have eq33345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq33297
    | exact resolve eq33297 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33297
  have eq33354 : False := by grind
  exact eq33354

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation3352 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq442 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
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
  have eq456 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq459 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3371 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq456
    | exact resolve eq456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq3413 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3371 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3371
    | (have j0 := eq3371 X0 X1
       grind)
    | exact resolve eq3371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3454 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq16
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq16 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3465 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq6802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3454
       have i₂ := eq3413 y x
       grind)
    | exact superpose eq3413 eq3454
    | (have j1 := eq3413 y x
       grind)
    | (have r₁ := eq3454
       have r₂ := eq3413 y x
       grind)
    | (have r₁ := eq3454
       have r₂ := eq3413 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3454
       have r₂ := eq3413 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3454 eq3413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413 eq3454
  have eq6803 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6802
  have eq6816 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3465 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3465
    | (have j0 := eq3465 (τ X0) (τ X1)
       grind)
    | exact resolve eq3465 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq6884 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6816 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6816
    | (have j0 := eq6816 X0 X1
       grind)
    | exact resolve eq6816 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq6919 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6884 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq6884
    | (have j0 := eq6884 X0 X1
       grind)
    | exact resolve eq6884 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884
  have eq6951 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6919 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6919
    | (have j0 := eq6919 X0 X1
       grind)
    | exact resolve eq6919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq6977 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6951 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6951
    | (have j0 := eq6951 X0 X1
       grind)
    | exact resolve eq6951 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq6996 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6977 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq6977
    | (have j0 := eq6977 X0 X1
       grind)
    | exact resolve eq6977 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6977
  have eq7013 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6996 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6996
    | (have j0 := eq6996 X0 X1
       grind)
    | exact resolve eq6996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996
  have eq7026 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7013 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7013
    | (have j0 := eq7013 X0 X1
       grind)
    | exact resolve eq7013 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq15696 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6803
       grind)
    | exact superpose eq6803 eq16
    | exact resolve eq16 eq6803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq15697 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15696
       have r₂ := eq22 x
       grind)
    | exact resolve eq15696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq15698 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15697
       grind)
    | exact superpose eq15697 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15697
       grind)
    | exact resolve eq13 eq15697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15697
  have eq15699 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15698
  have eq18110 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq16
    | exact resolve eq16 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15699
  have eq18111 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq18110
       have r₂ := eq22 x
       grind)
    | exact resolve eq18110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18114 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq442 x (σ y)
       have i₂ := eq18111
       grind)
    | exact superpose eq18111 eq442
    | (have j0 := eq442 x (σ y)
       grind)
    | (have r₁ := eq442 x (σ y)
       have r₂ := eq18111
       grind)
    | exact resolve eq442 eq18111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111
  have eq18123 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq18114
  have eq18124 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq18123
  have eq18127 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18124
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18124
    | exact resolve eq18124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18124
  have eq18137 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3465 x y
       have i₂ := eq18127
       grind)
    | exact superpose eq18127 eq3465
    | (have j0 := eq3465 x y
       grind)
    | (have r₁ := eq3465 x y
       have r₂ := eq18127
       grind)
    | exact resolve eq3465 eq18127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18127
  have eq18165 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq18137
  have eq18166 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq18165
  have eq18170 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3465 x y
       grind)
    | (have r₁ := eq18166
       have r₂ := eq3465 x y
       grind)
    | exact resolve eq18166 eq3465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3465 eq18166
  have eq18173 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18170
       grind)
    | exact superpose eq18170 eq16
    | exact resolve eq16 eq18170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18174 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq442 x (σ y)
       have i₂ := eq18170
       grind)
    | exact superpose eq18170 eq442
    | (have j0 := eq442 x (σ y)
       grind)
    | (have r₁ := eq442 x (σ y)
       have r₂ := eq18170
       grind)
    | exact resolve eq442 eq18170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq18170
  have eq18183 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq18174
  have eq18184 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq18183
  have eq18187 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18184
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18184
    | exact resolve eq18184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18184
  have eq18194 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18187
       grind)
    | exact superpose eq18187 eq10
    | exact resolve eq10 eq18187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18187
  have eq18353 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18194
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18194
    | exact resolve eq18194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194
  have eq18355 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18353
       grind)
    | exact superpose eq18353 eq16
    | exact resolve eq16 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353
  have eq18356 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq18355
       have r₂ := eq22 x
       grind)
    | exact resolve eq18355 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18355
  have eq18370 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18356
       grind)
    | exact superpose eq18356 eq10
    | exact resolve eq10 eq18356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18356
  have eq18530 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq18370
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq18370
    | exact resolve eq18370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq18559 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7026 x y
       have i₂ := eq18530
       grind)
    | exact superpose eq18530 eq7026
    | (have j0 := eq7026 x y
       grind)
    | (have r₁ := eq7026 x y
       have r₂ := eq18530
       grind)
    | exact resolve eq7026 eq18530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026 eq18530
  have eq18565 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq18559
  have eq18569 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18173
       have i₂ := eq18565
       grind)
    | exact superpose eq18565 eq18173
    | exact resolve eq18173 eq18565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173 eq18565
  have eq18575 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq18569
  have eq18576 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18575
       grind)
    | exact superpose eq18575 eq16
    | exact resolve eq16 eq18575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18575
  have eq18579 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq18576
       have r₂ := eq22 x
       grind)
    | exact resolve eq18576 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18576
  have eq18580 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18579
       grind)
    | exact superpose eq18579 eq16
    | exact resolve eq16 eq18579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18581 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18579
       grind)
    | exact superpose eq18579 eq10
    | exact resolve eq10 eq18579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18579
  have eq18740 : x = y := by
    first
    | (have i₁ := eq18581
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18581
    | exact resolve eq18581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18581
  have eq18741 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18580
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq18580
    | exact resolve eq18580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18580
  have eq18742 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18741
       have i₂ := eq18740
       grind)
    | exact superpose eq18740 eq18741
    | exact resolve eq18741 eq18740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740 eq18741
  have eq18743 : False := by grind
  exact eq18743
