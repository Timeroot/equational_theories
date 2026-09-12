import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq44
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq44 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq119 eq93
    | (have j0 := eq93 (σ x) (σ y)
       grind)
    | exact resolve eq93 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq126
  have eq221 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq51
    | exact resolve eq51 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq228 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (σ y) (M.op X0 X0))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq222 eq14
    | exact resolve eq14 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq235 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq228 eq51
    | exact resolve eq51 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) X0) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq228 eq14
    | exact resolve eq14 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq313 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51 eq237
    | exact resolve eq237 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq235 eq237
    | exact resolve eq237 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq237
  have eq325 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq316
  have eq370 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq313 eq325
    | exact resolve eq325 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq325
  have eq376 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq389 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq376 (σ x)
       grind)
    | exact resolve eq13 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq449 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 (M.op X1 X1) X0
       have i₂ := eq14 X1 X1 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1587 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq389 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq1589 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1587 eq49
    | exact resolve eq49 eq1587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1587
  have eq1593 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq1589
    | exact resolve eq1589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1589
  have eq1596 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq1593
       grind)
    | exact superpose eq1593 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1597 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1596
  have eq1621 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq475 x X0
       have i₂ := eq1597
       grind)
    | exact superpose eq1597 eq475
    | exact resolve eq475 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq1597
  have eq1819 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1621 y
       grind)
    | exact superpose eq1621 eq18
    | (have j1 := eq1621 y
       grind)
    | exact resolve eq18 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1621
  have eq1862 : y = (M.op x y) := by grind
  clear eq1819
  have eq1871 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1862 eq20
    | exact resolve eq20 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1886 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1871
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1871
    | exact resolve eq1871 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1871
  have eq2177 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op y (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq1862 eq221
    | exact resolve eq221 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq1862
  have eq2230 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2177 x x
       have i₂ := eq449 (M.op y (M.op x x)) X0
       grind)
    | (have i₁ := eq2177 x x
       have i₂ := eq449 X0 (M.op y (M.op x x))
       grind)
    | exact superpose eq449 eq2177
    | exact resolve eq2177 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq2234 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ x)) := by
    first
    | (have i₁ := eq51 (M.op y (M.op x x))
       have i₂ := eq2177 x x
       grind)
    | exact superpose eq2177 eq51
    | exact resolve eq51 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2177
  have eq2267 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ x)) := by
    first
    | exact superpose eq1886 eq2234
    | exact resolve eq2234 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq2234
  have eq2322 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2230 X0
       grind)
    | exact superpose eq2230 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq2230 x
       grind)
    | exact resolve eq13 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2328 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq2230 (M.op X0 X0)
       grind)
    | exact superpose eq2230 eq52
    | exact resolve eq52 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2349 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2328 X0 x
       have i₂ := eq2230 x
       grind)
    | exact superpose eq2230 eq2328
    | exact resolve eq2328 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2577 : x = (k x x) := by
    first
    | (have j0 := eq2322 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2579 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq43
    | exact resolve eq43 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2577
  have eq2583 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2579
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2579
    | exact resolve eq2579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2579
  have eq2586 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2583 eq93
    | (have j0 := eq93 (σ x) (σ x)
       grind)
    | exact resolve eq93 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2583
  have eq2587 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2586
  have eq2589 : x = (σ x) := by
    first
    | (have i₁ := eq2587
       have i₂ := eq2230 sF2
       grind)
    | exact superpose eq2230 eq2587
    | exact resolve eq2587 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq2587
  have eq2679 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) x) x) := by
    first
    | exact superpose eq2589 eq2267
    | exact resolve eq2267 eq2589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267 eq2589
  have eq2681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2679
       have i₂ := eq2349 sF4
       grind)
    | exact superpose eq2349 eq2679
    | exact resolve eq2679 eq2349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349 eq2679
  have eq2690 : False := by grind
  exact eq2690

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_y_pxy_y_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  clear eq36
  have eq50 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op X2 X2) = X3 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq50 X0 X1 X3
       grind)
    | exact superpose eq50 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq50 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ (M.op X2 X2) = X3 := by
    intro X2 X3
    first
    | (have j0 := eq325 x x X2 X3
       grind)
    | (have r₁ := eq325 x x X2 X3
       have r₂ := eq50 x x X2
       grind)
    | exact resolve eq325 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq325
  have eq351 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    grind
  have eq429 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (M.op X1 X1)
       have i₂ := eq351 X1 (τ X0)
       grind)
    | exact superpose eq351 eq39
    | exact resolve eq39 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq351
  have eq433 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq429
    | exact resolve eq429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq1510 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq334 y x
       grind)
    | exact superpose eq334 eq45
    | (have j1 := eq334 y x
       grind)
    | exact resolve eq45 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1535 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1510
    | exact resolve eq1510 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1536 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq1535
    | exact resolve eq1535 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1536 eq334
    | (have j0 := eq334 (σ y) (σ x)
       grind)
    | exact resolve eq334 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq1546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq1541
    | exact resolve eq1541 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1553 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1546
       have r₂ := eq28
       grind)
    | exact resolve eq1546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq1566 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  have eq1575 : ∀ X0 : G, x = (M.op y y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1553 eq333
    | exact resolve eq333 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1638 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1566 eq1536
    | exact resolve eq1536 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq1566
  have eq1643 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1638
  have eq1701 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq333 y X0
       have i₂ := eq1643
       grind)
    | exact superpose eq1643 eq333
    | exact resolve eq333 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1835 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1701 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1701
    | (have j0 := eq1701 y
       grind)
    | exact resolve eq1701 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1701
  have eq1896 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1835 eq30
    | exact resolve eq30 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1835
  have eq1915 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1896
    | exact resolve eq1896 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1896
  have eq1916 : y = (M.op x y) := by grind
  clear eq1915
  have eq1918 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1916 eq21
    | exact resolve eq21 eq1916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1916
  have eq1937 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1918
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1918
    | exact resolve eq1918 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1918
  have eq1938 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1937 eq27
    | exact resolve eq27 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2395 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq1575 X1
       have i₂ := eq316 X0 y
       grind)
    | (have i₁ := eq1575 X1
       have i₂ := eq316 y X0
       grind)
    | exact superpose eq316 eq1575
    | (have j0 := eq1575 X1
       grind)
    | exact resolve eq1575 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq1575
  have eq3012 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq2395 eq27
    | (have j1 := eq2395 X0 (σ y)
       grind)
    | exact resolve eq27 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2395
  have eq3074 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq1937 eq3012
    | (have j0 := eq3012 X0
       grind)
    | exact resolve eq3012 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq3012
  have eq3078 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq3074 X0
       grind)
    | (have r₁ := eq3074 X0
       have r₂ := eq28
       grind)
    | exact resolve eq3074 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq3111 : ∀ X1 : G, (M.op x X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq333 x X1
       have i₂ := eq3078 x
       grind)
    | exact superpose eq3078 eq333
    | exact resolve eq333 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq3113 : ∀ X1 : G, (k (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq433 X1 x
       have i₂ := eq3078 x
       grind)
    | exact superpose eq3078 eq433
    | exact resolve eq433 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq3153 : ∀ X1 : G, (k (σ x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq3113 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3113
    | (have j0 := eq3113 X1
       grind)
    | exact resolve eq3113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3113
  have eq3465 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3153 eq83
    | (have j0 := eq83 (σ x)
       grind)
    | exact resolve eq83 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq3153
  have eq3475 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3465
  have eq3486 : x = (σ x) := by
    first
    | (have i₁ := eq3475
       have i₂ := eq3078 sF2
       grind)
    | exact superpose eq3078 eq3475
    | exact resolve eq3475 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078 eq3475
  have eq3723 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq3486 eq1938
    | exact resolve eq1938 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938 eq3486
  have eq3731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3723
       have i₂ := eq3111 sF1
       grind)
    | (have i₁ := eq3723
       have i₂ := eq3111 (M.op x sF1)
       grind)
    | exact superpose eq3111 eq3723
    | exact resolve eq3723 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111 eq3723
  have eq3740 : False := by grind
  exact eq3740

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq85 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq328 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq328 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq328 X0 X1
       grind)
    | exact superpose eq328 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq328 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq328 X1 X1
       grind)
    | exact resolve eq12 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq401 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0)
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq50
    | (have j1 := eq106 (σ x)
       grind)
    | exact resolve eq50 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq106
  have eq440 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq53 X1 X0 X2 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X1 (M.op X1 X1) X2
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq553 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq213
  have eq566 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq342 (σ X0) (σ X0)
       grind)
    | exact superpose eq342 eq553
    | exact resolve eq553 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq574 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq566 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq566
    | exact resolve eq566 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq740 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X1
       have i₂ := eq328 X0 (σ X1)
       grind)
    | (have i₁ := eq574 X1
       have i₂ := eq328 (σ X1) X0
       grind)
    | exact superpose eq328 eq574
    | exact resolve eq574 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4281 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X1 (τ (M.op X1 X1))
       have i₂ := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq372 eq740
    | (have j1 := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq740 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq4297 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq372 X0 x
       grind)
    | exact superpose eq372 eq44
    | (have j1 := eq372 X0 x
       grind)
    | exact resolve eq44 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4321 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq4325 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq4414 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq4325 x X2
       have i₂ := eq4325 x X0
       grind)
    | exact superpose eq4325 eq4325
    | exact resolve eq4325 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4484 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq4325 X0 X1
       grind)
    | exact superpose eq4325 eq15
    | exact resolve eq15 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4673 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq342 x X2
       have i₂ := eq4484 X0 x
       grind)
    | exact superpose eq4484 eq342
    | exact resolve eq342 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5253 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq440 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq449 X1 X0 x
       grind)
    | exact superpose eq449 eq440
    | exact resolve eq440 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5259 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5253 x X1 x
       have i₂ := eq461 x sF0 x
       grind)
    | exact superpose eq461 eq5253
    | exact resolve eq5253 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5408 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq450 eq440
    | exact resolve eq440 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5414 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5408 x X1 x
       have i₂ := eq461 x sF4 x
       grind)
    | exact superpose eq461 eq5408
    | exact resolve eq5408 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5612 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 (σ X0)
       have i₂ := eq401 X0
       grind)
    | exact superpose eq401 eq328
    | (have j1 := eq401 X0
       grind)
    | exact resolve eq328 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq6712 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op (M.op X2 X2) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq449 eq447
    | exact resolve eq447 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq6715 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op (M.op X2 X2) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq450 eq447
    | exact resolve eq447 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq6963 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq440 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq447 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq440 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq447 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq447 eq440
    | exact resolve eq440 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq447
  have eq7097 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6963 X0 X1 x X3 x
       have i₂ := eq461 x (M.op X0 X1) x
       grind)
    | exact superpose eq461 eq6963
    | exact resolve eq6963 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6963
  have eq7188 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6715 X0 X1 x X3 X4 X5
       have i₂ := eq342 x (M.op X5 X5)
       grind)
    | exact superpose eq342 eq6715
    | exact resolve eq6715 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715
  have eq7190 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6712 X0 X1 x X3 X4 X5
       have i₂ := eq342 x (M.op X5 X5)
       grind)
    | exact superpose eq342 eq6712
    | exact resolve eq6712 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq7246 : ∀ X0 X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7188 X0 X1 X3 x X0
       have i₂ := eq461 X0 sF4 x
       grind)
    | exact superpose eq461 eq7188
    | exact resolve eq7188 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7248 : ∀ X0 X1 X3 : G, (M.op x y) = (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7190 X0 X1 X3 x X0
       have i₂ := eq461 X0 sF0 x
       grind)
    | exact superpose eq461 eq7190
    | exact resolve eq7190 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7190
  have eq7271 : ∀ X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | exact superpose eq5414 eq7246
    | exact resolve eq7246 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246
  have eq7272 : ∀ X1 X3 : G, (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op X1 X1))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq7248 x X1 X3
       have i₂ := eq5259 x
       grind)
    | exact superpose eq5259 eq7248
    | exact resolve eq7248 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7248
  have eq7962 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq448 X0 X1 x x X4 X5
       have i₂ := eq461 x (M.op X0 X1) x
       grind)
    | exact superpose eq461 eq448
    | exact resolve eq448 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq8266 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) (M.op X4 X4)) = X1 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq461 X4 X1 x
       have i₂ := eq7962 X0 X1 x X2
       grind)
    | exact superpose eq7962 eq461
    | exact resolve eq461 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X3 X3))) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq7962 X0 (M.op X1 X2) x X3
       grind)
    | exact superpose eq7962 eq14
    | exact resolve eq14 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8365 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op X1 X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x
       have i₂ := eq7962 X0 sF0 x x
       grind)
    | exact superpose eq7962 eq51
    | exact resolve eq51 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq8372 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 X1))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x
       have i₂ := eq7962 X0 sF4 x x
       grind)
    | exact superpose eq7962 eq52
    | exact resolve eq52 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq7962
  have eq36890 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 X0))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq8372 X1 x
       have i₂ := eq7097 X1 X0 x
       grind)
    | (have i₁ := eq8372 X1 X1
       have i₂ := eq7097 X1 X1 x
       grind)
    | exact superpose eq7097 eq8372
    | exact resolve eq8372 eq7097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097 eq8372
  have eq54311 : ∀ X0 X2 : G, (M.op (M.op (M.op x X0) (M.op y (M.op x y))) (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq8266 x X0 x X2
       have i₂ := eq5259 x
       grind)
    | exact superpose eq5259 eq8266
    | exact resolve eq8266 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5259 eq8266
  have eq55322 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (M.op X0 X1)) (M.op (σ y) (M.op (σ x) (σ y)))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq5414 eq8345
    | exact resolve eq8345 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57471 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0
       have i₂ := eq5612 X0 X1
       grind)
    | exact superpose eq5612 eq574
    | (have j1 := eq5612 X0 X1
       grind)
    | exact resolve eq574 eq5612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq5612
  have eq57720 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57471 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq57471
    | (have j0 := eq57471 X0 X1
       grind)
    | exact resolve eq57471 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57471
  have eq71714 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op y x)) (M.op X0 (M.op X1 X1))) y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8345 X0 y y X1
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq8345
    | exact resolve eq8345 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq71725 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71714 x x
       have i₂ := eq8345 x y x x
       grind)
    | exact superpose eq8345 eq71714
    | exact resolve eq71714 eq8345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8345 eq71714
  have eq262413 : ∀ X0 : G, (k x x) = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq409
       have i₂ := eq4325 X0 sF2
       grind)
    | exact superpose eq4325 eq409
    | exact resolve eq409 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq263646 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5649 x
       have i₂ := eq262413 X0
       grind)
    | exact superpose eq262413 eq5649
    | (have j0 := eq5649 x
       grind)
    | exact resolve eq5649 eq262413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649 eq262413
  have eq264517 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq263646 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263646
    | (have j0 := eq263646 X0
       grind)
    | exact resolve eq263646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263646
  have eq264563 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq264517 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq264517
    | (have j0 := eq264517 X0
       grind)
    | exact resolve eq264517 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264517
  have eq264564 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq264563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264563
  have eq288235 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op X0 X0) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq4297 X1
       have i₂ := eq4484 X1 X0
       grind)
    | exact superpose eq4484 eq4297
    | (have j0 := eq4297 X1
       grind)
    | exact resolve eq4297 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4297 eq4484
  have eq289634 : ∀ X0 : G, x ≠ (k (σ x) (σ x)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq288235 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288235
  have eq472103 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq57720 x X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq57720
    | (have j0 := eq57720 x x
       grind)
    | exact resolve eq57720 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq57720
  have eq474012 : ∀ X0 X1 : G, x ≠ (M.op X0 X0) ∨ (M.op X1 X1) = x ∨ x = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq472103 eq289634
    | (have j0 := eq289634 X1
       grind)
    | exact resolve eq289634 eq472103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289634 eq472103
  have eq475352 : ∀ X0 X1 : G, x ≠ (M.op X0 X0) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have j0 := eq474012 X0 X1
       have j1 := eq4321 X1 x
       grind)
    | (have r₁ := eq474012 X0 X1
       have r₂ := eq4321 X0 x
       grind)
    | (have r₁ := eq474012 X0 X1
       have r₂ := eq4321 X0 x
       grind)
    | exact resolve eq474012 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321 eq474012
  have eq475444 : ∀ X0 X2 : G, x ≠ (τ (M.op X0 X0)) ∨ (M.op X2 X2) = x := by
    intro X0 X2
    first
    | (have i₁ := eq475352 x X2
       have i₂ := eq4325 x X0
       grind)
    | exact superpose eq4325 eq475352
    | (have j0 := eq475352 X0 X2
       grind)
    | exact resolve eq475352 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325 eq475352
  have eq574429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq71725 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71725
  have eq574430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq574429
    | exact resolve eq574429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq574429
  have eq574442 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq574430
       have r₂ := eq28
       grind)
    | exact resolve eq574430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574430
  have eq574965 : (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq574442 eq55322
    | exact resolve eq55322 eq574442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574442
  have eq574968 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq55322 eq574965
    | exact resolve eq574965 eq55322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55322 eq574965
  have eq575069 : ∀ X0 : G, (τ (σ x)) = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq574968 eq4414
    | exact resolve eq4414 eq574968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4414 eq574968
  have eq575669 : ∀ X0 : G, x = (τ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq575069
    | exact resolve eq575069 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575069
  have eq575692 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq475444 x y
       grind)
    | (have r₁ := eq575669 x
       have r₂ := eq475444 x x
       grind)
    | exact resolve eq575669 eq475444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475444 eq575669
  have eq575950 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op X0 X0))) x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7272 X0 y
       have i₂ := eq575692
       grind)
    | exact superpose eq575692 eq7272
    | exact resolve eq7272 eq575692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272 eq575692
  have eq576294 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq8365 eq575950
    | exact resolve eq575950 eq8365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365 eq575950
  have eq577365 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq576294 eq30
    | exact resolve eq30 eq576294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq576294
  have eq577623 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq577365
    | exact resolve eq577365 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq577365
  have eq577624 : y = (M.op x y) ∨ x = y := by grind
  clear eq577623
  have eq577627 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq577624 eq21
    | exact resolve eq21 eq577624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577864 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) (M.op y y)) (M.op X1 X1)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq577624 eq54311
    | exact resolve eq54311 eq577624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54311 eq577624
  have eq577894 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq577864 X0 x
       have i₂ := eq461 x (M.op x X0) y
       grind)
    | exact superpose eq461 eq577864
    | exact resolve eq577864 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq577864
  have eq578064 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq577627
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq577627
    | exact resolve eq577627 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577627
  have eq578838 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq264564 x
       have i₂ := eq577894 x
       grind)
    | exact superpose eq577894 eq264564
    | exact resolve eq264564 eq577894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264564 eq577894
  have eq579471 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq578838
       have r₂ := eq23
       grind)
    | exact resolve eq578838 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578838
  have eq591543 : (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) (σ x)) ∨ x = y := by
    first
    | exact superpose eq579471 eq36890
    | exact resolve eq36890 eq579471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36890 eq579471
  have eq591552 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq591543
       have i₂ := eq14 sF4 sF2 sF2
       grind)
    | exact superpose eq14 eq591543
    | exact resolve eq591543 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591543
  have eq591954 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq591552 eq28
    | exact resolve eq28 eq591552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591552
  have eq592056 : x = y := by
    first
    | (have r₁ := eq591954
       have r₂ := eq578064
       grind)
    | exact resolve eq591954 eq578064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578064 eq591954
  have eq592559 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq592056
       grind)
    | exact superpose eq592056 eq19
    | exact resolve eq19 eq592056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq592560 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq592056
       grind)
    | exact superpose eq592056 eq25
    | exact resolve eq25 eq592056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq592056
  have eq592964 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq592560
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq592560
    | exact resolve eq592560 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq592560
  have eq593319 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq592559
       have i₂ := eq328 X0 x
       grind)
    | (have i₁ := eq592559
       have i₂ := eq328 x X0
       grind)
    | exact superpose eq328 eq592559
    | exact resolve eq592559 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq593582 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7271 X0 x
       have i₂ := eq592559
       grind)
    | exact superpose eq592559 eq7271
    | exact resolve eq7271 eq592559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271 eq592559
  have eq594010 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq592964 eq593582
    | exact resolve eq593582 eq592964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593582
  have eq594202 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq5414 eq594010
    | exact resolve eq594010 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq594010
  have eq594275 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq592964 eq594202
    | exact resolve eq594202 eq592964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592964 eq594202
  have eq594315 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq594275
       have i₂ := eq342 (M.op sF2 sF4) sF0
       grind)
    | exact superpose eq342 eq594275
    | exact resolve eq594275 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq594275
  have eq594334 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq594315 eq28
    | exact resolve eq28 eq594315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq594315
  have eq595766 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4673 X0 (σ (M.op X0 X0))
       have i₂ := eq593319 (σ (M.op X0 X0))
       grind)
    | exact superpose eq593319 eq4673
    | exact resolve eq4673 eq593319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq595892 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq595766 x
       have i₂ := eq593319 x
       grind)
    | exact superpose eq593319 eq595766
    | exact resolve eq595766 eq593319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593319 eq595766
  have eq596992 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq595892
    | exact resolve eq595892 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq595892
  have eq597650 : False := by grind
  exact eq597650

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  clear eq35
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq393 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq38
    | exact resolve eq38 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq445 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq343
    | exact resolve eq343 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq343
  have eq467 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X1 X1) X0)) X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X2
       have i₂ := eq178 X0 X1 (σ X2)
       grind)
    | exact superpose eq178 eq467
    | exact resolve eq467 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq707 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op (M.op X1 X1) X0))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X2
       have i₂ := eq178 X0 X1 (τ X2)
       grind)
    | exact superpose eq178 eq425
    | exact resolve eq425 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq709 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq711 : ∀ X0 X2 : G, (k (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq707 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq707
    | exact resolve eq707 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : ∀ X0 X2 : G, (k (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq706 X0 x X2
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq706
    | exact resolve eq706 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq699 X0 x X2 X3
       have i₂ := eq709 x X0
       grind)
    | exact superpose eq709 eq699
    | (have j0 := eq699 X0 x X2 X3
       grind)
    | (have r₁ := eq699 (M.op X0 X0) x X2 (M.op (M.op x x) (M.op X0 X0))
       have r₂ := eq709 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq699 X0 x X2 (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0)))
       have r₂ := eq709 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq699 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq709
  have eq829 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ (M.op X1 X1))
       have i₂ := eq711 X1 (τ X0)
       grind)
    | exact superpose eq711 eq38
    | exact resolve eq38 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq842 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq829
    | exact resolve eq829 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq895 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq897 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq914 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq698 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq698 X1 X1
       grind)
    | exact resolve eq12 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq914 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq2057 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X1 (σ (M.op X1 X1))
       have i₂ := eq927 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq927 eq711
    | (have j1 := eq927 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq711 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2058 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq927 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq927 eq842
    | (have j1 := eq927 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq842 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2067 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq2074 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2058 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2075 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2057 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2184 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq2075 (M.op X1 X1) X0
       grind)
    | exact superpose eq2075 eq16
    | exact resolve eq16 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2759 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2184 X1 (σ (M.op X1 X1))
       have i₂ := eq2074 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq2074 eq2184
    | exact resolve eq2184 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq2184
  have eq4487 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (τ (k (σ x) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ (M.op X1 X1))
       have i₂ := eq2759 X1 X0
       grind)
    | exact superpose eq2759 eq44
    | exact resolve eq44 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq4503 : ∀ X0 X1 : G, (k x (σ (M.op X1 X1))) = (k x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq44 eq4487
    | exact resolve eq4487 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq4487
  have eq5266 : ∀ X0 : G, y = (M.op (M.op (M.op y x) (M.op X0 X0)) y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq895
       grind)
    | exact superpose eq895 eq16
    | exact resolve eq16 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq5269 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5266 x
       have i₂ := eq16 x y x
       grind)
    | exact superpose eq16 eq5266
    | exact resolve eq5266 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5266
  have eq5405 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (M.op X0 X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq897 eq16
    | exact resolve eq16 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq5408 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5405 x
       have i₂ := eq16 sF2 sF3 x
       grind)
    | exact superpose eq16 eq5405
    | exact resolve eq5405 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5405
  have eq23087 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5269
       grind)
    | exact superpose eq5269 eq40
    | exact resolve eq40 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5269
  have eq23090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23087
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23087
    | exact resolve eq23087 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23087
  have eq23092 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq23090
    | exact resolve eq23090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23090
  have eq33964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23092 eq5408
    | exact resolve eq5408 eq23092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408 eq23092
  have eq33973 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33964
       have r₂ := eq27
       grind)
    | exact resolve eq33964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33964
  have eq34005 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq33973 eq712
    | exact resolve eq712 eq33973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq33973
  have eq34342 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq34005
    | exact resolve eq34005 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34005
  have eq34418 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34342 X0
       have j1 := eq719 X0 X0 x
       grind)
    | (have r₁ := eq34342 (M.op X0 X0)
       have r₂ := eq719 X0 x (k x (M.op X0 X0))
       grind)
    | (have r₁ := eq34342 X0
       have r₂ := eq719 y x x
       grind)
    | exact resolve eq34342 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq34342
  have eq34559 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k x (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq4503 X1 X0
       have i₂ := eq34418 (σ (M.op X0 X0))
       grind)
    | exact superpose eq34418 eq4503
    | exact resolve eq4503 eq34418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503
  have eq34570 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2067 X0 x
       have i₂ := eq34418 x
       grind)
    | exact superpose eq34418 eq2067
    | (have j0 := eq2067 X0 x
       grind)
    | (have r₁ := eq2067 X0 x
       have r₂ := eq34418 x
       grind)
    | exact resolve eq2067 eq34418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq34581 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34570 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34570
  have eq34598 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34581 eq34559
    | exact resolve eq34559 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34559
  have eq34614 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34418 eq34598
    | exact resolve eq34598 eq34418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34418 eq34598
  have eq34626 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34581 eq34614
    | exact resolve eq34614 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34614
  have eq34633 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq34626
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34626
    | exact resolve eq34626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34626
  have eq34636 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq34633 eq31
    | exact resolve eq31 eq34633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34736 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq34636
    | exact resolve eq34636 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34636
  have eq34737 : x = (σ x) ∨ x = y := by grind
  clear eq34736
  have eq34743 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq34737
       grind)
    | exact superpose eq34737 eq18
    | exact resolve eq18 eq34737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34737
  have eq35316 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq34581 (M.op X0 X0)
       grind)
    | exact superpose eq34581 eq16
    | exact resolve eq16 eq34581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34581
  have eq35385 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq34633 eq35316
    | exact resolve eq35316 eq34633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34633 eq35316
  have eq36457 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq35385 eq34743
    | exact resolve eq34743 eq35385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34743
  have eq36460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq35385 eq26
    | (have j1 := eq35385 (σ y)
       grind)
    | exact resolve eq26 eq35385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35385
  have eq36694 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq36457
  have eq37382 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36460 eq27
    | exact resolve eq27 eq36460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36460
  have eq37443 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq36694 eq31
    | exact resolve eq31 eq36694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36694
  have eq37543 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq37443
    | exact resolve eq37443 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37443
  have eq37544 : y = (M.op x y) ∨ x = y := by grind
  clear eq37543
  have eq37582 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq37544
       grind)
    | exact superpose eq37544 eq24
    | exact resolve eq24 eq37544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37544
  have eq37634 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq37582
    | exact resolve eq37582 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37582
  have eq37696 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37634 eq37382
    | (have r₁ := eq37382
       have r₂ := eq37634
       grind)
    | exact resolve eq37382 eq37634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37382 eq37634
  have eq37697 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq37696
  have eq37698 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq37697
  have eq37745 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq37698 eq31
    | exact resolve eq31 eq37698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq37698
  have eq37855 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq37745
    | exact resolve eq37745 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37745
  have eq37856 : x = y := by grind
  clear eq37855
  have eq37896 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37856
       grind)
    | exact superpose eq37856 eq18
    | exact resolve eq18 eq37856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37897 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq37856
       grind)
    | exact superpose eq37856 eq24
    | exact resolve eq24 eq37856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37856
  have eq37935 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37897
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37897
    | exact resolve eq37897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37897
  have eq37942 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37935 eq26
    | exact resolve eq26 eq37935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37935
  have eq38563 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq698 x X0
       have i₂ := eq37896
       grind)
    | exact superpose eq37896 eq698
    | exact resolve eq698 eq37896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38620 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2075 X0 x
       have i₂ := eq37896
       grind)
    | exact superpose eq37896 eq2075
    | exact resolve eq2075 eq37896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq37896
  have eq38872 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq38620
    | (have j0 := eq38620 X0
       grind)
    | exact resolve eq38620 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38620
  have eq38984 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq38872 x
       have i₂ := eq38563 x
       grind)
    | exact superpose eq38563 eq38872
    | exact resolve eq38872 eq38563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38872
  have eq39487 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37942 eq698
    | exact resolve eq698 eq37942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq37942
  have eq39834 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39487 x
       have i₂ := eq38563 x
       grind)
    | exact superpose eq38563 eq39487
    | exact resolve eq39487 eq38563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38563 eq39487
  have eq40227 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq39834 eq27
    | exact resolve eq27 eq39834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39834
  have eq40271 : False := by grind
  exact eq40271

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X1 X1)) (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq360 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq387 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq303
    | exact resolve eq303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq536 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x x X1
       have i₂ := eq177 x x X0
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X0)) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq177 X0 X1 X2
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op (M.op X1 X1) X0))
       have r₂ := eq177 X0 X1 (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq177 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq548 : ∀ X0 X2 X3 : G, (M.op X0 X0) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq540 X0 x X2 X3
       have i₂ := eq544 x X0
       grind)
    | exact superpose eq544 eq540
    | (have j0 := eq540 X0 x X2 X3
       grind)
    | (have r₁ := eq540 (M.op X0 X0) x (M.op (M.op x x) (M.op X0 X0)) X3
       have r₂ := eq544 X0 (M.op (M.op x x) (M.op X0 X0))
       grind)
    | (have r₁ := eq540 X0 x (M.op (M.op X0 X0) (M.op X0 (M.op (M.op x x) X0))) X3
       have r₂ := eq544 X0 (M.op X0 (M.op (M.op x x) X0))
       grind)
    | exact resolve eq540 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq597 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq544 X0 (M.op X0 X0)
       grind)
    | exact superpose eq544 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq544 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X2
       have i₂ := eq544 X1 X0
       grind)
    | exact superpose eq544 eq16
    | exact resolve eq16 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq607 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq615 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 (M.op X1 X1)
       have i₂ := eq607 X1 (σ X0)
       grind)
    | exact superpose eq607 eq360
    | exact resolve eq360 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq607
  have eq630 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq615
    | exact resolve eq615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq792 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq793 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq536 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq536 X0 X1
       grind)
    | exact superpose eq536 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq536 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq536 X1 X1
       grind)
    | exact resolve eq12 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq1570 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X1
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq536
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq536 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1583 : ∀ X0 X1 : G, (k X1 (τ (k X0 X0))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X1 X0
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq630
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq630 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq1737 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq630 (τ (M.op X1 X1)) X1
       have i₂ := eq839 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq839 eq630
    | (have j1 := eq839 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq630 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq1745 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1749 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1785 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1749 x X2
       have i₂ := eq1749 x X0
       grind)
    | exact superpose eq1749 eq1749
    | exact resolve eq1749 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1749 X1 X2
       have i₂ := eq839 X2 X0
       grind)
    | exact superpose eq839 eq1749
    | (have j1 := eq839 X1 (τ (k X0 X0))
       grind)
    | exact resolve eq1749 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1815 : ∀ X0 X2 X3 : G, (τ (M.op X0 X0)) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq548 x X2 X3
       have i₂ := eq1749 x X0
       grind)
    | exact superpose eq1749 eq548
    | (have j0 := eq548 X0 X2 X3
       grind)
    | (have r₁ := eq548 X0 (τ (M.op x x)) X3
       have r₂ := eq1749 X0 x
       grind)
    | exact resolve eq548 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1884 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (σ X2)) = (σ (k (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op X1 X1) X2
       have i₂ := eq1749 X0 X1
       grind)
    | exact superpose eq1749 eq34
    | exact resolve eq34 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq2204 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq39
    | exact resolve eq39 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq2205 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2204
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2204
    | exact resolve eq2204 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2205
    | exact resolve eq2205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq3570 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1745 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1745
    | (have j0 := eq1745 X1 (σ X0)
       grind)
    | exact resolve eq1745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3571 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1745 X1 (τ X0)
       have i₂ := eq387 X0 X0
       grind)
    | exact superpose eq387 eq1745
    | (have j0 := eq1745 X1 (τ X0)
       grind)
    | exact resolve eq1745 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq20855 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X2 X2)) = (M.op (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X1 X1)) (M.op x (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq178
  have eq20864 : ∀ X2 X3 : G, (M.op y (M.op X2 X2)) = (M.op (M.op x y) (M.op x (M.op X3 X3))) := by
    intro X2 X3
    first
    | (have i₁ := eq20855 X2 x X2 X3
       have i₂ := eq605 sF0 x X2
       grind)
    | exact superpose eq605 eq20855
    | exact resolve eq20855 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq27880 : ∀ X0 X2 : G, y = (M.op (M.op (M.op x y) (M.op x (M.op X0 X0))) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq605 y X2 x
       have i₂ := eq20864 x X0
       grind)
    | exact superpose eq20864 eq605
    | exact resolve eq605 eq20864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20864
  have eq64733 : ∀ X0 X1 : G, (τ (k X1 X1)) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1796 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq65114 : ∀ X0 : G, (σ x) ≠ (k x x) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq97 eq64733
    | (have j0 := eq64733 X0 (σ x)
       grind)
    | exact resolve eq64733 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq64733
  have eq100020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2207 eq793
    | exact resolve eq793 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100029 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq100020
       have r₂ := eq27
       grind)
    | exact resolve eq100020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100020
  have eq100036 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1570 eq100029
    | (have j1 := eq1570 x x
       grind)
    | exact resolve eq100029 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100029
  have eq100044 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100036 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq100036
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq100036
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq100036
       grind)
    | exact resolve eq12 eq100036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100036
  have eq100073 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq65114 (σ x)
       grind)
    | (have r₁ := eq100044
       have r₂ := eq65114 x
       grind)
    | exact resolve eq100044 eq65114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65114 eq100044
  have eq100088 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq100073
       have r₂ := eq26
       grind)
    | exact resolve eq100073 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100073
  have eq100100 : (σ x) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1570 eq100088
    | (have j1 := eq1570 x x
       grind)
    | exact resolve eq100088 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570 eq100088
  have eq100108 : (σ x) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2207 eq100100
    | exact resolve eq100100 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207 eq100100
  have eq100115 : (σ x) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq100108
       have r₂ := eq27
       grind)
    | exact resolve eq100108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100108
  have eq100144 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1583 x X0
       have i₂ := eq100115
       grind)
    | exact superpose eq100115 eq1583
    | (have j0 := eq1583 x x
       grind)
    | exact resolve eq1583 eq100115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq100115
  have eq100166 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq100144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100144
  have eq100191 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq100166
    | exact resolve eq100166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100166
  have eq100214 : ∀ X0 : G, (M.op x y) = (M.op y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq100191 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq100191 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq100191 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100191
  have eq100232 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq100214 X0
       grind)
    | (have i₁ := eq12 X0 x
       have i₂ := eq100214 (M.op X0 x)
       grind)
    | exact superpose eq100214 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq100214 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq100214 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq100214 X0
       grind)
    | exact resolve eq12 eq100214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100214
  have eq100253 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq100232 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq100232 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq100232 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100232
  have eq100259 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq100253 X0
       grind)
    | (have r₁ := eq100253 X0
       have r₂ := eq18
       grind)
    | exact resolve eq100253 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100253
  have eq100265 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 y
       have i₂ := eq100259 X0
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq100259 X0
       grind)
    | exact superpose eq100259 eq39
    | (have j1 := eq100259 X0
       grind)
    | exact resolve eq39 eq100259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq100259
  have eq100268 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq100265 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100265
    | (have j0 := eq100265 X0
       grind)
    | exact resolve eq100265 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100265
  have eq100272 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq100268
    | (have j0 := eq100268 X0
       grind)
    | exact resolve eq100268 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100268
  have eq100335 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq793
       have i₂ := eq100272 (k sF3 sF2)
       grind)
    | exact superpose eq100272 eq793
    | (have j1 := eq100272 X0
       grind)
    | exact resolve eq793 eq100272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq100344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq100335 X0
       grind)
    | (have r₁ := eq100335 X0
       have r₂ := eq27
       grind)
    | exact resolve eq100335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100335
  have eq134457 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq100344 (M.op X0 x)
       grind)
    | exact superpose eq100344 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq100344 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq100344 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq100344 X0
       grind)
    | exact resolve eq12 eq100344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100344
  have eq134477 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq134457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134457
  have eq134495 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq134477 X0
       grind)
    | (have r₁ := eq134477 X0
       have r₂ := eq26
       grind)
    | exact resolve eq134477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134477
  have eq134512 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq100272 eq134495
    | (have j0 := eq134495 X0
       have j1 := eq100272 X0
       grind)
    | exact resolve eq134495 eq100272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100272 eq134495
  have eq134525 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq134512 X0
       grind)
    | (have r₁ := eq134512 X0
       have r₂ := eq27
       grind)
    | exact resolve eq134512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134512
  have eq134625 : ∀ X0 X1 : G, (τ (σ x)) = (τ (M.op X0 X0)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1785 X0 x
       have i₂ := eq134525 (M.op X0 X0)
       grind)
    | exact superpose eq134525 eq1785
    | (have j1 := eq134525 X1
       grind)
    | exact resolve eq1785 eq134525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq134525
  have eq135014 : ∀ X0 X1 : G, x = (τ (M.op X0 X0)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | exact superpose eq29 eq134625
    | (have j0 := eq134625 X0 X1
       grind)
    | exact resolve eq134625 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq134625
  have eq135171 : ∀ X1 : G, (k X1 x) = X1 := by
    intro X1
    first
    | (have j0 := eq135014 x X1
       have j1 := eq1815 x x X1
       grind)
    | (have r₁ := eq135014 x X1
       have r₂ := eq1815 x x x
       grind)
    | (have r₁ := eq135014 x (τ (M.op x x))
       have r₂ := eq1815 x (k (τ (M.op x x)) x) x
       grind)
    | exact resolve eq135014 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq135014
  have eq135314 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1745 X0 x
       have i₂ := eq135171 x
       grind)
    | exact superpose eq135171 eq1745
    | (have j0 := eq1745 X0 x
       grind)
    | (have r₁ := eq1745 X0 x
       have r₂ := eq135171 x
       grind)
    | exact resolve eq1745 eq135171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq135320 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3570 x X0
       have i₂ := eq135171 x
       grind)
    | exact superpose eq135171 eq3570
    | (have j0 := eq3570 x X0
       grind)
    | exact resolve eq3570 eq135171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570
  have eq135321 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq3571 x X0
       have i₂ := eq135171 x
       grind)
    | exact superpose eq135171 eq3571
    | (have j0 := eq3571 x X0
       grind)
    | exact resolve eq3571 eq135171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq135335 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1884 X0 X1 x
       have i₂ := eq135171 (M.op X0 X0)
       grind)
    | exact superpose eq135171 eq1884
    | exact resolve eq1884 eq135171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq135350 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq135171 (τ X0)
       grind)
    | exact superpose eq135171 eq34
    | exact resolve eq34 eq135171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq135171
  have eq135441 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have j0 := eq135321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135321
  have eq135442 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq135320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135320
  have eq135443 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq135314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135314
  have eq135487 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq135350 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq135350
    | (have j0 := eq135350 X0
       grind)
    | exact resolve eq135350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135350
  have eq135502 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq135335 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq135335
    | (have j0 := eq135335 X0 X1
       grind)
    | exact resolve eq135335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135335
  have eq135511 : (σ x) = (τ x) := by
    first
    | (have i₁ := eq135442 x
       have i₂ := eq135441 x
       grind)
    | exact superpose eq135441 eq135442
    | exact resolve eq135442 eq135441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135442
  have eq135550 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq135487 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq135487
    | exact resolve eq135487 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135487
  have eq135555 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (τ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq135502 X0 x
       have i₂ := eq135441 x
       grind)
    | exact superpose eq135441 eq135502
    | exact resolve eq135502 eq135441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135502
  have eq135557 : (σ x) = (τ x) := by
    first
    | (have i₁ := eq135511
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq135511
    | exact resolve eq135511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq135511
  have eq135570 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | exact superpose eq135550 eq135555
    | exact resolve eq135555 eq135550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135550 eq135555
  have eq135578 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135570 X0
       have i₂ := eq135557
       grind)
    | exact superpose eq135557 eq135570
    | exact resolve eq135570 eq135557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135557 eq135570
  have eq135582 : (σ x) = (σ (τ x)) := by
    first
    | (have i₁ := eq135578 x
       have i₂ := eq135441 x
       grind)
    | exact superpose eq135441 eq135578
    | exact resolve eq135578 eq135441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135441 eq135578
  have eq135583 : x = (σ x) := by
    first
    | (have i₁ := eq135582
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq135582
    | exact resolve eq135582 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135582
  have eq138317 : ∀ X1 : G, y = (M.op (M.op (M.op x y) (M.op x x)) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq27880 x X1
       have i₂ := eq135443 x
       grind)
    | exact superpose eq135443 eq27880
    | exact resolve eq27880 eq135443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27880
  have eq138438 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq135443 (M.op X0 X0)
       grind)
    | exact superpose eq135443 eq16
    | exact resolve eq16 eq135443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135443
  have eq138549 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq138438 X0
       have i₂ := eq135583
       grind)
    | exact superpose eq135583 eq138438
    | exact resolve eq138438 eq135583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135583 eq138438
  have eq138659 : y = (M.op x y) := by
    first
    | (have i₁ := eq138317 x
       have i₂ := eq605 sF0 x x
       grind)
    | exact superpose eq605 eq138317
    | exact resolve eq138317 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq138317
  have eq140065 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq138659
       grind)
    | exact superpose eq138659 eq24
    | exact resolve eq24 eq138659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq138659
  have eq140294 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq140065 eq20
    | exact resolve eq20 eq140065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq140065
  have eq141392 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138549 eq26
    | (have j1 := eq138549 (σ y)
       grind)
    | exact resolve eq26 eq138549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq138549
  have eq142832 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq141392 eq27
    | exact resolve eq27 eq141392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq141392
  have eq142913 : False := by grind
  exact eq142913

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x x X1
       have i₂ := eq178 x x X0
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X2
       have i₂ := eq545 X1 X0
       grind)
    | exact superpose eq545 eq16
    | exact resolve eq16 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq545 X0 (M.op X0 X0)
       grind)
    | exact superpose eq545 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq545 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq610 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq598 X0 X1 X2
       have i₂ := eq608 X1 (M.op X0 (M.op X2 X2))
       grind)
    | exact superpose eq608 eq598
    | exact resolve eq598 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq613 : ∀ X0 X1 X2 : G, (k (k X0 (M.op X2 X2)) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq610 X0 X1 X2
       have i₂ := eq608 X2 X0
       grind)
    | exact superpose eq608 eq610
    | exact resolve eq610 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq636 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X1) (M.op X2 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq608 X2 (M.op X0 X1)
       grind)
    | exact superpose eq608 eq16
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 (M.op X1 X1)
       have i₂ := eq608 X1 (M.op X0 X0)
       grind)
    | exact superpose eq608 eq545
    | exact resolve eq545 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op X1 X1) X0 X2
       have i₂ := eq608 X1 (M.op X0 X0)
       grind)
    | exact superpose eq608 eq178
    | exact resolve eq178 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq640 : ∀ X0 : G, y = (M.op (k (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq175
    | exact resolve eq175 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 : G, (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq608 X0 sF4
       grind)
    | exact superpose eq608 eq176
    | exact resolve eq176 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq639 X0 X1 X2
       have i₂ := eq545 X1 (k (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq545 eq639
    | exact resolve eq639 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq687 : ∀ X0 X1 X3 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq613 (k X0 (M.op X3 X3)) X1 x
       have i₂ := eq613 X0 x X3
       grind)
    | exact superpose eq613 eq613
    | exact resolve eq613 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
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
  have eq950 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq952 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq916 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq916 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq916 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq985 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq41
    | exact resolve eq41 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq986 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq985
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq985
    | exact resolve eq985 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq985
  have eq988 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq986
    | exact resolve eq986 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq999 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq952 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq952
    | (have j0 := eq952 (σ X0)
       grind)
    | exact resolve eq952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq988 eq950
    | exact resolve eq950 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1043 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1036
       have r₂ := eq27
       grind)
    | exact resolve eq1036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1048 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1043 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1043
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1043
       grind)
    | exact resolve eq12 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1043 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1052 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1048
  have eq1054 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1049
    | exact resolve eq1049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1055 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq988 eq1052
    | exact resolve eq1052 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1058 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1054 eq108
    | exact resolve eq108 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1054
  have eq1061 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1058
    | exact resolve eq1058 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1077 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1055 eq608
    | exact resolve eq608 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1292 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1077 eq26
    | (have j1 := eq1077 (σ x)
       grind)
    | exact resolve eq26 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq988 eq1292
    | exact resolve eq1292 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq1292
  have eq1336 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1303
       have r₂ := eq27
       grind)
    | exact resolve eq1303 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1358 : ∀ X0 : G, x = (M.op (k x (M.op X0 X0)) y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq636 y x X0
       have i₂ := eq1336
       grind)
    | exact superpose eq1336 eq636
    | exact resolve eq636 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1391 : ∀ X0 X1 : G, y = (M.op (k x (M.op X1 X1)) (k x (M.op X0 X0))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq636 (k x (M.op X0 X0)) y X1
       have i₂ := eq1358 X0
       grind)
    | exact superpose eq1358 eq636
    | exact resolve eq636 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq2479 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq177 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq177 X1 X0 X2 X4
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2603 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (k X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2479 X0 X1 X2 X3 X4 X5
       have i₂ := eq608 X5 X0
       grind)
    | exact superpose eq608 eq2479
    | exact resolve eq2479 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2684 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (k (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (k X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2603 X0 X1 X2 X3 X4 X5
       have i₂ := eq608 X3 (M.op (M.op X0 X1) (M.op X2 X2))
       grind)
    | exact superpose eq608 eq2603
    | exact resolve eq2603 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2741 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (k (k (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (k X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2684 X0 X1 X2 X3 X4 X5
       have i₂ := eq608 X2 (M.op X0 X1)
       grind)
    | exact superpose eq608 eq2684
    | exact resolve eq2684 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2787 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (k X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq2741 X0 X1 x x X4 X5
       have i₂ := eq613 (M.op X0 X1) x x
       grind)
    | exact superpose eq613 eq2741
    | exact resolve eq2741 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq3460 : ∀ X0 : G, y = (M.op X0 X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq537 (k x (M.op x x)) X0
       have i₂ := eq1391 x x
       grind)
    | exact superpose eq1391 eq537
    | exact resolve eq537 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq3463 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq608 (k x (M.op X0 X0)) x
       have i₂ := eq1391 X0 X0
       grind)
    | exact superpose eq1391 eq608
    | exact resolve eq608 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3473 : ∀ X0 X2 : G, (M.op X0 X0) = (k y (M.op X2 X2)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X2
    first
    | (have i₁ := eq642 (k x (M.op x x)) X2 X0
       have i₂ := eq1391 x x
       grind)
    | exact superpose eq1391 eq642
    | exact resolve eq642 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq3475 : ∀ X0 X1 : G, (k X0 y) = (k X0 (M.op X1 X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X1 (k x (M.op x x))
       have i₂ := eq1391 x x
       grind)
    | exact superpose eq1391 eq687
    | exact resolve eq687 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq1391
  have eq3524 : ∀ X0 : G, (M.op X0 X0) = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3475 eq3473
    | exact resolve eq3473 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473 eq3475
  have eq3563 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3460 eq3524
    | exact resolve eq3524 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq3833 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3563
       grind)
    | exact superpose eq3563 eq41
    | exact resolve eq41 eq3563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3842 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3833
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3833
    | exact resolve eq3833 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq3851 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3842 eq965
    | (have j0 := eq965 (σ y) X0
       grind)
    | (have r₁ := eq965 (σ y) x
       have r₂ := eq3842
       grind)
    | exact resolve eq965 eq3842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq3852 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3842 eq952
    | (have j0 := eq952 (σ y)
       grind)
    | (have r₁ := eq952 (σ y)
       have r₂ := eq3842
       grind)
    | exact resolve eq952 eq3842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3842
  have eq3853 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3852
  have eq3854 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq3851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq3902 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3853 eq3460
    | exact resolve eq3460 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460 eq3853
  have eq3906 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by grind
  clear eq3902
  have eq4958 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3463 x
       grind)
    | exact superpose eq3463 eq18
    | (have j1 := eq3463 x
       grind)
    | exact resolve eq18 eq3463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq4994 : (M.op x y) = (k x (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3906 eq4958
    | exact resolve eq4958 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958
  have eq5485 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3854 eq26
    | (have j1 := eq3854 (σ x)
       grind)
    | exact resolve eq26 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq5678 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5485 eq99
    | exact resolve eq99 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq5485
  have eq5706 : (τ (M.op (σ x) (σ y))) = (k x (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3906 eq5678
    | exact resolve eq5678 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906 eq5678
  have eq5709 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4994 eq5706
    | exact resolve eq5706 eq4994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994 eq5706
  have eq5717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5709 eq14
    | exact resolve eq14 eq5709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5709
  have eq5719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq5717
    | exact resolve eq5717 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq5722 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5719
       have r₂ := eq27
       grind)
    | exact resolve eq5719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719
  have eq5723 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq5722 eq29
    | exact resolve eq29 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq5750 : x = (M.op x y) := by
    first
    | exact superpose eq5723 eq30
    | exact resolve eq30 eq5723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5755 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5723 eq14
    | exact resolve eq14 eq5723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq5756 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq18
    | exact resolve eq18 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5761 : ∀ X0 : G, y = (M.op (k (M.op x y) (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq640 X0
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq640
    | exact resolve eq640 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq5763 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1061
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq1061
    | exact resolve eq1061 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq5827 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op y (M.op X0 X0)) (M.op (M.op x y) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq5756 eq177
    | exact resolve eq177 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5833 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op y (M.op X0 X0)) (k (M.op x y) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5827 X0 X0
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq5827
    | exact resolve eq5827 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827
  have eq5834 : ∀ X0 X1 : G, (M.op x y) = (M.op (k y (M.op X0 X0)) (k (M.op x y) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5833 X0 X1
       have i₂ := eq608 X0 y
       grind)
    | exact superpose eq608 eq5833
    | exact resolve eq5833 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5833
  have eq9945 : ∀ X0 X1 X2 X3 : G, (k y (M.op X2 X2)) = (M.op (M.op (k (M.op x y) (M.op X0 X0)) (M.op X1 X1)) (M.op (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq5834 eq177
    | exact resolve eq177 eq5834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834
  have eq9949 : ∀ X0 X1 X2 X3 : G, (k y (M.op X2 X2)) = (M.op (M.op (k (M.op x y) (M.op X0 X0)) (M.op X1 X1)) (k (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9945 X0 X1 X2 X0
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq9945
    | exact resolve eq9945 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9945
  have eq9957 : ∀ X0 X1 X2 X3 : G, (k y (M.op X2 X2)) = (M.op (k (k (M.op x y) (M.op X0 X0)) (M.op X1 X1)) (k (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9949 X0 X0 X2 X3
       have i₂ := eq608 X0 (k sF0 (M.op X0 X0))
       grind)
    | exact superpose eq608 eq9949
    | exact resolve eq9949 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9949
  have eq9958 : ∀ X2 X3 : G, (k y (M.op X2 X2)) = (M.op (M.op x y) (k (M.op x y) (M.op X3 X3))) := by
    intro X2 X3
    first
    | (have i₁ := eq9957 X2 x X2 X3
       have i₂ := eq613 sF0 x X2
       grind)
    | exact superpose eq613 eq9957
    | exact resolve eq9957 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq10057 : ∀ X0 X1 X2 : G, (k (M.op x y) (M.op X1 X1)) = (M.op (k (k y (M.op X0 X0)) (M.op X2 X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9958 eq636
    | exact resolve eq636 eq9958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10060 : ∀ X1 : G, (k (M.op x y) (M.op X1 X1)) = (M.op y (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq10057 x X1 x
       have i₂ := eq613 y x x
       grind)
    | exact superpose eq613 eq10057
    | exact resolve eq10057 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10057
  have eq10113 : ∀ X0 : G, (k y (M.op X0 X0)) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10060 eq9958
    | exact resolve eq9958 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq10115 : y = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq10060 eq5761
    | exact resolve eq5761 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761
  have eq10122 : ∀ X1 : G, (M.op x y) = (k (M.op y (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq10060 eq613
    | exact resolve eq613 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10131 : y = (M.op (k y (M.op x y)) (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq10115
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq10115
    | (have j1 := eq28 y (M.op x y)
       grind)
    | exact resolve eq10115 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10136 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op y (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq10115 eq177
    | exact resolve eq177 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10140 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op X0 X0)) (k y (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10136 X0 X1
       have i₂ := eq608 X1 y
       grind)
    | exact superpose eq608 eq10136
    | exact resolve eq10136 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10136
  have eq10142 : y = (M.op (k y (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5756 eq10131
    | exact resolve eq10131 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10131
  have eq10143 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (k (M.op x y) (M.op X0 X0)) (k y (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10140 X0 X1
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq10140
    | exact resolve eq10140 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10140
  have eq10144 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (k y (M.op X1 X1))) := by
    intro X1
    first
    | exact superpose eq10060 eq10143
    | exact resolve eq10143 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10143
  have eq10147 : ∀ X0 : G, (M.op x y) = (k (k y (M.op x y)) (M.op X0 X0)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq10122 x
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq10122
    | (have j1 := eq28 y (M.op x y)
       grind)
    | exact resolve eq10122 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10189 : ∀ X0 : G, (M.op x y) = (k (k y (M.op x y)) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5756 eq10147
    | (have j0 := eq10147 X0
       grind)
    | exact resolve eq10147 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10147
  have eq10196 : ∀ X0 X1 : G, (k y (M.op x y)) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op y (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq10142 eq177
    | exact resolve eq177 eq10142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10142
  have eq10201 : ∀ X0 X1 : G, (k y (M.op x y)) = (M.op (M.op (M.op x y) (M.op X0 X0)) (k y (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq10196 X0 X1
       have i₂ := eq608 X1 y
       grind)
    | exact superpose eq608 eq10196
    | exact resolve eq10196 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10196
  have eq10203 : ∀ X0 X1 : G, (k y (M.op x y)) = (M.op (k (M.op x y) (M.op X0 X0)) (k y (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq10201 X0 X1
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq10201
    | exact resolve eq10201 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10205 : ∀ X1 : G, (k y (M.op x y)) = (M.op (M.op y (M.op x y)) (k y (M.op X1 X1))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq10060 eq10203
    | exact resolve eq10203 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10203
  have eq10206 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10144 eq10205
    | exact resolve eq10205 eq10144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10256 : ∀ X1 : G, y = (k (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq613 y X1 x
       have i₂ := eq10113 x
       grind)
    | exact superpose eq10113 eq613
    | exact resolve eq613 eq10113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10476 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5763 eq10189
    | exact resolve eq10189 eq5763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5763
  have eq10520 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq10060 eq10476
    | exact resolve eq10476 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10476
  have eq10521 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10520
  have eq10526 : ∀ X0 : G, (k y (M.op X0 X0)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10521 eq10113
    | exact resolve eq10113 eq10521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10113
  have eq10528 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10521 eq10115
    | exact resolve eq10115 eq10521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10115
  have eq10530 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10521 eq10206
    | exact resolve eq10206 eq10521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10206
  have eq10531 : ∀ X0 : G, y = (k (M.op (M.op x y) (M.op x y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10521 eq10256
    | exact resolve eq10256 eq10521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10521
  have eq10541 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10530
  have eq10548 : ∀ X0 : G, y = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10531 x
       have i₂ := eq638 sF0 x
       grind)
    | exact superpose eq638 eq10531
    | exact resolve eq10531 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10531
  have eq10551 : ∀ X0 : G, y = (k y (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10528 eq10526
    | exact resolve eq10526 eq10528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10526
  have eq10556 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10548 eq10551
    | exact resolve eq10551 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10551
  have eq10591 : (σ y) = (M.op (k (M.op (σ x) (σ y)) y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10528 eq641
    | exact resolve eq641 eq10528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10617 : (M.op x y) = (k (k y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10528 eq10189
    | exact resolve eq10189 eq10528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10189 eq10528
  have eq10628 : (M.op x y) = (k (k y (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10617
  have eq10633 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10541 eq10628
    | exact resolve eq10628 eq10541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10541 eq10628
  have eq10949 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq10556
       grind)
    | exact superpose eq10556 eq41
    | exact resolve eq41 eq10556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10556
  have eq10961 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10949
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10949
    | exact resolve eq10949 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10949
  have eq11191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10633 eq41
    | exact resolve eq41 eq10633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq10633
  have eq11193 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11191
    | exact resolve eq11191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11191
  have eq11196 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5722 eq11193
    | exact resolve eq11193 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11193
  have eq11237 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10961 eq952
    | (have j0 := eq952 (σ y)
       grind)
    | (have r₁ := eq952 (σ y)
       have r₂ := eq10961
       grind)
    | exact resolve eq952 eq10961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq11243 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11237
  have eq11494 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11243 eq180
    | exact resolve eq180 eq11243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11535 : y = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11243 eq10548
    | exact resolve eq10548 eq11243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11243
  have eq11541 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq11535
  have eq11568 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11494 X0
       have i₂ := eq545 sF3 (M.op sF4 (M.op X0 X0))
       grind)
    | exact superpose eq545 eq11494
    | exact resolve eq11494 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11494
  have eq11596 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11568 X0
       have i₂ := eq608 X0 sF4
       grind)
    | exact superpose eq608 eq11568
    | exact resolve eq11568 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11568
  have eq11616 : (σ x) = (k (M.op (σ x) (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10548 eq11596
    | exact resolve eq11596 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11596
  have eq11631 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11541 eq11616
    | exact resolve eq11616 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616
  have eq11654 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq11541 eq27
    | exact resolve eq27 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11681 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq5722 eq11654
    | exact resolve eq11654 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11654
  have eq13317 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) y) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq10591 eq177
    | exact resolve eq177 eq10591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10591
  have eq13322 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) y) = (M.op (M.op (σ x) (M.op X0 X0)) (k (σ y) (M.op X1 X1))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13317 X0 X0
       have i₂ := eq608 X0 sF3
       grind)
    | exact superpose eq608 eq13317
    | exact resolve eq13317 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13317
  have eq13327 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) y) = (M.op (k (σ x) (M.op X0 X0)) (k (σ y) (M.op X1 X1))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13322 X0 X1
       have i₂ := eq608 X0 sF2
       grind)
    | exact superpose eq608 eq13322
    | exact resolve eq13322 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13322
  have eq13332 : ∀ X0 : G, (k (M.op (σ x) (σ y)) y) = (M.op (k (σ x) (M.op X0 X0)) (k (σ y) y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10548 eq13327
    | exact resolve eq13327 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13327
  have eq13336 : (k (M.op (σ x) (σ y)) y) = (M.op (k (σ x) y) (k (σ y) y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10548 eq13332
    | exact resolve eq13332 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10548 eq13332
  have eq13338 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11541 eq13336
    | exact resolve eq13336 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13336
  have eq13339 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10961 eq13338
    | exact resolve eq13338 eq10961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961 eq13338
  have eq13340 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11196 eq13339
    | exact resolve eq13339 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196 eq13339
  have eq13341 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13340
    | exact resolve eq13340 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13340
  have eq13342 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11631 eq13341
    | exact resolve eq13341 eq11631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11631 eq13341
  have eq26710 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (k (k (M.op (σ x) (σ y)) (M.op X1 X1)) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq641 eq2787
    | exact resolve eq2787 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26850 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op y (M.op x y)) X0) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq10122 eq2787
    | exact resolve eq2787 eq10122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26863 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq10060 eq2787
    | exact resolve eq2787 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26989 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x y)) (k X0 (M.op X1 X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq175 x
       have i₂ := eq2787 X0 sF0 x x
       grind)
    | exact superpose eq2787 eq175
    | exact resolve eq175 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq27023 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x y)) (k X0 (M.op X1 X1))) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq26989 X0 X1
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq26989
    | exact resolve eq26989 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26989
  have eq27179 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq26710 X0 x x
       have i₂ := eq613 sF4 x x
       grind)
    | exact superpose eq613 eq26710
    | exact resolve eq26710 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26710
  have eq27329 : ∀ X0 : G, (k (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq27179 X0
       have i₂ := eq608 X0 sF2
       grind)
    | exact superpose eq608 eq27179
    | exact resolve eq27179 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27179
  have eq27759 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (k (k (M.op (M.op x y) X0) (M.op X1 X1)) (M.op X2 X2))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27023 (k (M.op sF0 X1) (M.op X2 X2)) X1
       have i₂ := eq636 sF0 X1 X2
       grind)
    | exact superpose eq636 eq27023
    | exact resolve eq27023 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27833 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k X0 (M.op X1 X1)) (M.op x y)) X0) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq27023 (k X0 (M.op X1 X1)) x
       have i₂ := eq613 X0 x X1
       grind)
    | exact superpose eq613 eq27023
    | exact resolve eq27023 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27023
  have eq27904 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq27759 X0 x x
       have i₂ := eq613 (M.op sF0 X0) x x
       grind)
    | exact superpose eq613 eq27759
    | exact resolve eq27759 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27759
  have eq28038 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op y (M.op X2 X2))) = (M.op X1 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq27904 eq177
    | exact resolve eq177 eq27904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28050 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (k y (M.op X2 X2))) = (M.op X1 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28038 X0 X1 X2
       have i₂ := eq608 X2 y
       grind)
    | exact superpose eq608 eq28038
    | exact resolve eq28038 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq28074 : ∀ X0 X1 X2 : G, (M.op (k (M.op x y) (M.op X0 X0)) (k y (M.op X2 X2))) = (M.op X1 (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28050 X0 X1 X2
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq28050
    | exact resolve eq28050 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28050
  have eq28084 : ∀ X1 X2 : G, (M.op (M.op y (M.op x y)) (k y (M.op X2 X2))) = (M.op X1 (M.op (M.op x y) X1)) := by
    intro X1 X2
    first
    | exact superpose eq10060 eq28074
    | exact resolve eq28074 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28074
  have eq28090 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq10144 eq28084
    | exact resolve eq28084 eq10144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10144 eq28084
  have eq28113 : ∀ X0 X1 X2 : G, (M.op y (M.op x y)) = (M.op (M.op X2 X2) (M.op (M.op X0 (M.op x y)) (k X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28090 (M.op x x)
       have i₂ := eq2787 X0 sF0 x x
       grind)
    | exact superpose eq2787 eq28090
    | exact resolve eq28090 eq2787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28090
  have eq28176 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28113 X0 X1 X0
       have i₂ := eq545 X0 (M.op (M.op X0 sF0) (k X0 (M.op X1 X1)))
       grind)
    | exact superpose eq545 eq28113
    | exact resolve eq28113 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28113
  have eq28293 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op y (M.op X3 X3))) = (M.op (M.op (k X1 (M.op X2 X2)) (M.op x y)) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq27833 eq177
    | exact resolve eq177 eq27833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833
  have eq28305 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (k y (M.op X3 X3))) = (M.op (M.op (k X1 (M.op X2 X2)) (M.op x y)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28293 X0 X1 X2 X3
       have i₂ := eq608 X3 y
       grind)
    | exact superpose eq608 eq28293
    | exact resolve eq28293 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28293
  have eq28339 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op x y) (M.op X0 X0)) (k y (M.op X3 X3))) = (M.op (M.op (k X1 (M.op X2 X2)) (M.op x y)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28305 X0 X1 X2 X3
       have i₂ := eq608 X0 sF0
       grind)
    | exact superpose eq608 eq28305
    | exact resolve eq28305 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28305
  have eq28353 : ∀ X1 X2 X3 : G, (M.op (M.op y (M.op x y)) (k y (M.op X3 X3))) = (M.op (M.op (k X1 (M.op X2 X2)) (M.op x y)) X1) := by
    intro X1 X2 X3
    first
    | exact superpose eq10060 eq28339
    | exact resolve eq28339 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28339
  have eq28358 : ∀ X1 X2 : G, (M.op y (M.op x y)) = (M.op (M.op (k X1 (M.op X2 X2)) (M.op x y)) X1) := by
    intro X1 X2
    first
    | exact superpose eq28176 eq28353
    | exact resolve eq28353 eq28176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28176 eq28353
  have eq28453 : ∀ X0 X1 X2 : G, (M.op (k (M.op y (M.op x y)) (M.op X2 X2)) (M.op (k X0 (M.op X1 X1)) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq28358 eq636
    | exact resolve eq636 eq28358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28358
  have eq28484 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (k X0 (M.op X1 X1)) (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq10122 eq28453
    | exact resolve eq28453 eq10122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10122 eq28453
  have eq28652 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq28484 eq177
    | exact resolve eq177 eq28484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28654 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) = (M.op X0 (k (M.op x y) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq28484 eq2787
    | exact resolve eq2787 eq28484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28662 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10060 eq28654
    | exact resolve eq28654 eq10060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060 eq28654
  have eq28663 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) (k X0 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28652 X0 X1 X2 X3
       have i₂ := eq608 X3 X0
       grind)
    | exact superpose eq608 eq28652
    | exact resolve eq28652 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28652
  have eq28684 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y (M.op x y))) = (k (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28662 X0 X1 X0
       have i₂ := eq608 X0 (M.op (k X0 (M.op X1 X1)) sF0)
       grind)
    | exact superpose eq608 eq28662
    | exact resolve eq28662 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28662
  have eq28685 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (k (M.op (k X0 (M.op X1 X1)) (M.op x y)) (M.op X2 X2)) (k X0 (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28663 X0 X1 X0 X3
       have i₂ := eq608 X0 (M.op (k X0 (M.op X1 X1)) sF0)
       grind)
    | exact superpose eq608 eq28663
    | exact resolve eq28663 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28663
  have eq28691 : ∀ X0 X3 : G, (M.op x y) = (M.op (M.op X0 (M.op y (M.op x y))) (k X0 (M.op X3 X3))) := by
    intro X0 X3
    first
    | exact superpose eq28684 eq28685
    | exact resolve eq28685 eq28684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28684 eq28685
  have eq29472 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op X0 (k (k (M.op (M.op y (M.op x y)) X0) (M.op X1 X1)) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28691 (k (M.op (M.op y sF0) X1) (M.op X2 X2)) x
       have i₂ := eq636 (M.op y sF0) X1 X2
       grind)
    | exact superpose eq636 eq28691
    | exact resolve eq28691 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq29611 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op y (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq29472 X0 x x
       have i₂ := eq613 (M.op (M.op y sF0) X0) x x
       grind)
    | exact superpose eq613 eq29472
    | exact resolve eq29472 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq29472
  have eq30457 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq608 X1 X0
       have i₂ := eq26863 X0 X1
       grind)
    | exact superpose eq26863 eq608
    | exact resolve eq608 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30567 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) (M.op X3 X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 (M.op X1 X1) X0 X3 X2
       have i₂ := eq26863 X0 X1
       grind)
    | exact superpose eq26863 eq177
    | exact resolve eq177 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30577 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op y (M.op x y))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x
       have i₂ := eq26863 (M.op X0 X1) x
       grind)
    | exact superpose eq26863 eq16
    | exact resolve eq16 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30604 : (σ y) = (M.op (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq26863 sF4 x
       grind)
    | exact superpose eq26863 eq176
    | exact resolve eq176 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq30661 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (k (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) (M.op X3 X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30567 X0 X1 X2 X0
       have i₂ := eq608 X0 (M.op (M.op sF0 X0) (M.op y sF0))
       grind)
    | exact superpose eq608 eq30567
    | exact resolve eq30567 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30567
  have eq30833 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X2) (k (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) (M.op X3 X3))) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq30661 X0 x X2 X3
       have i₂ := eq545 x (M.op X2 X2)
       grind)
    | exact superpose eq545 eq30661
    | exact resolve eq30661 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30661
  have eq30977 : ∀ X0 X3 : G, (k (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) (M.op X3 X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq30833 X0 X0 X3
       have i₂ := eq545 X0 (k (M.op (M.op sF0 X0) (M.op y sF0)) (M.op X3 X3))
       grind)
    | exact superpose eq545 eq30833
    | exact resolve eq30833 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30833
  have eq31200 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) X0) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq26863 X0 x
       have i₂ := eq26850 X0 x
       grind)
    | exact superpose eq26850 eq26863
    | exact resolve eq26863 eq26850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26863
  have eq31324 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y (M.op x y)) (M.op X0 X1)) (M.op x y)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x
       have i₂ := eq26850 (M.op X0 X1) x
       grind)
    | exact superpose eq26850 eq16
    | exact resolve eq16 eq26850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26850
  have eq32169 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq28484 X0 x
       have i₂ := eq30457 X0 x
       grind)
    | exact superpose eq30457 eq28484
    | exact resolve eq28484 eq30457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32200 : y = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x y)))) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq10256 x
       have i₂ := eq30457 (M.op sF0 (M.op y sF0)) x
       grind)
    | exact superpose eq30457 eq10256
    | exact resolve eq10256 eq30457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10256 eq30457
  have eq33241 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30977 eq28484
    | exact resolve eq28484 eq30977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33997 : (σ x) = (M.op (M.op (M.op (M.op y (M.op x y)) (σ y)) (M.op x y)) (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq30604 eq31324
    | exact resolve eq31324 eq30604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30604 eq31324
  have eq34297 : (σ x) = (M.op (M.op (M.op (M.op y (M.op x y)) (σ y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y)))) := by
    first
    | exact superpose eq33241 eq33997
    | exact resolve eq33997 eq33241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33997
  have eq34414 : (σ x) = (M.op (M.op (M.op (M.op x y) (σ y)) (M.op y (M.op x y))) (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y)))) := by
    first
    | exact superpose eq31200 eq34297
    | exact resolve eq34297 eq31200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31200 eq34297
  have eq34499 : (σ x) = (M.op (M.op (M.op x y) (M.op (σ y) (M.op x y))) (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y)))) := by
    first
    | exact superpose eq33241 eq34414
    | exact resolve eq34414 eq33241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34414
  have eq36131 : ∀ X0 X1 : G, (k (M.op (M.op x y) (M.op X0 (M.op x y))) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq33241 eq30977
    | exact resolve eq30977 eq33241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30977
  have eq36135 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op x y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq33241 eq30577
    | exact resolve eq30577 eq33241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30577
  have eq36677 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op x y) (M.op (σ y) (M.op x y))) (k (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq641 eq36135
    | exact resolve eq36135 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq36135
  have eq37266 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y))) (M.op X0 X0)) (M.op (σ x) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq34499 eq177
    | exact resolve eq177 eq34499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq34499
  have eq37286 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y))) (M.op X0 X0)) (k (σ x) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37266 X0 X0
       have i₂ := eq608 X0 sF2
       grind)
    | exact superpose eq608 eq37266
    | exact resolve eq37266 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37266
  have eq37293 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y))) (M.op X0 X0)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27329 eq37286
    | exact resolve eq37286 eq27329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27329 eq37286
  have eq37299 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op (k (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op x y))) (M.op X0 X0)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq37293 X0
       have i₂ := eq608 X0 (M.op sF0 (M.op sF4 sF0))
       grind)
    | exact superpose eq608 eq37293
    | exact resolve eq37293 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37293
  have eq37302 : (M.op (M.op x y) (M.op (σ y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq36131 eq37299
    | exact resolve eq37299 eq36131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36131 eq37299
  have eq37318 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (M.op x y) (M.op (σ y) (M.op x y))) (k (M.op (σ x) (σ y)) (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq37302 eq2787
    | exact resolve eq2787 eq37302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2787 eq37302
  have eq37332 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq36677 eq37318
    | exact resolve eq37318 eq36677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36677 eq37318
  have eq37340 : ∀ X0 : G, (σ x) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37332 X0
       have i₂ := eq608 X0 (M.op sF3 sF4)
       grind)
    | exact superpose eq608 eq37332
    | exact resolve eq37332 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37332
  have eq37348 : ∀ X0 : G, (σ x) = (k (M.op (σ y) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13342 eq37340
    | exact resolve eq37340 eq13342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13342
  have eq37349 : ∀ X0 : G, (σ x) = (k (M.op (σ y) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq11541 eq37340
    | exact resolve eq37340 eq11541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37410 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq37340 eq28484
    | exact resolve eq28484 eq37340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28484
  have eq37411 : (M.op x y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (σ x)) := by
    first
    | exact superpose eq37340 eq28691
    | exact resolve eq28691 eq37340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28691 eq37340
  have eq37440 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq37349 x
       have i₂ := eq638 sF3 x
       grind)
    | exact superpose eq638 eq37349
    | exact resolve eq37349 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37349
  have eq37441 : ∀ X0 : G, (σ x) = (M.op X0 X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37348 x
       have i₂ := eq638 sF3 x
       grind)
    | exact superpose eq638 eq37348
    | exact resolve eq37348 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37348
  have eq37469 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op (σ x) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq37410 eq33241
    | exact resolve eq33241 eq37410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33241 eq37410
  have eq37863 : ∀ X1 : G, (σ x) = (k (M.op X1 X1) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq638 x x
       have i₂ := eq37441 x
       grind)
    | exact superpose eq37441 eq638
    | exact resolve eq638 eq37441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq38147 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37441 eq37863
    | exact resolve eq37863 eq37441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37863
  have eq38506 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq37440 (M.op X0 X0)
       grind)
    | exact superpose eq37440 eq16
    | exact resolve eq16 eq37440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37440
  have eq39385 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38147 eq999
    | (have j0 := eq999 (σ x)
       grind)
    | exact resolve eq999 eq38147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38147
  have eq39414 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39385
  have eq39431 : (σ x) = (σ (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37441 eq39414
    | exact resolve eq39414 eq37441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441 eq39414
  have eq39480 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39431 eq15
    | exact resolve eq15 eq39431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39431
  have eq39558 : x = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq39480
    | exact resolve eq39480 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39480
  have eq39577 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq39558
       have i₂ := eq5750
       grind)
    | exact superpose eq5750 eq39558
    | exact resolve eq39558 eq5750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5750 eq39558
  have eq39590 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq39577 eq27
    | exact resolve eq27 eq39577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39616 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq39577 eq11541
    | exact resolve eq11541 eq39577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11541 eq39577
  have eq39636 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq39616
  have eq39652 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq39636
       have r₂ := eq11681
       grind)
    | exact resolve eq39636 eq11681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11681 eq39636
  have eq39657 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq39590
       have r₂ := eq5722
       grind)
    | exact resolve eq39590 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39590
  have eq39668 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39657 eq26
    | exact resolve eq26 eq39657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41736 : (M.op x y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op y (M.op x y))) (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39652 eq37411
    | exact resolve eq37411 eq39652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37411 eq39652
  have eq41772 : (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op (σ x) (M.op x y)) (M.op x y))) (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37469 eq41736
    | exact resolve eq41736 eq37469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37469 eq41736
  have eq41831 : (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38506 eq41772
    | exact resolve eq41772 eq38506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38506 eq41772
  have eq41860 : y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27904 eq41831
    | exact resolve eq41831 eq27904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27904 eq41831
  have eq41861 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq41860
  have eq41926 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5756
       have i₂ := eq41861
       grind)
    | exact superpose eq41861 eq5756
    | exact resolve eq5756 eq41861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41861
  have eq42253 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41926 eq39668
    | exact resolve eq39668 eq41926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39668 eq41926
  have eq42290 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42253
  have eq42348 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42290 eq27
    | exact resolve eq27 eq42290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42290
  have eq42425 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5722 eq42348
    | exact resolve eq42348 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42348
  have eq42445 : y = (M.op x y) := by
    first
    | (have r₁ := eq42425
       have r₂ := eq39657
       grind)
    | exact resolve eq42425 eq39657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39657 eq42425
  have eq42466 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq42445
       grind)
    | exact superpose eq42445 eq24
    | exact resolve eq24 eq42445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq42514 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5756
       have i₂ := eq42445
       grind)
    | exact superpose eq42445 eq5756
    | exact resolve eq5756 eq42445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq42561 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq29611 X0
       have i₂ := eq42445
       grind)
    | exact superpose eq42445 eq29611
    | exact resolve eq29611 eq42445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29611
  have eq42571 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op x y))) (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq32169 X0
       have i₂ := eq42445
       grind)
    | exact superpose eq42445 eq32169
    | exact resolve eq32169 eq42445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32169
  have eq42572 : (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq32200
       have i₂ := eq42445
       grind)
    | exact superpose eq42445 eq32200
    | exact resolve eq32200 eq42445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32200 eq42445
  have eq42583 : (M.op x y) = (k (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq42572
       have i₂ := eq608 sF0 (M.op sF0 (M.op sF0 (M.op sF0 sF0)))
       grind)
    | exact superpose eq608 eq42572
    | exact resolve eq42572 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq42572
  have eq42584 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42571 X0
       have i₂ := eq16 X0 sF0 sF0
       grind)
    | exact superpose eq16 eq42571
    | exact resolve eq42571 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42571
  have eq42594 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq42561 x
       have i₂ := eq545 sF0 x
       grind)
    | exact superpose eq545 eq42561
    | exact resolve eq42561 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq42561
  have eq42636 : (σ x) = (σ y) := by
    first
    | exact superpose eq5755 eq42466
    | exact resolve eq42466 eq5755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42466
  have eq42641 : (M.op x y) = (k (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq42514 eq42583
    | exact resolve eq42583 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42583
  have eq42667 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq42584 eq42641
    | exact resolve eq42641 eq42584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42584 eq42641
  have eq42687 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42514 eq42667
    | exact resolve eq42667 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42514 eq42667
  have eq42729 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq42636 eq26
    | exact resolve eq26 eq42636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq42636
  have eq42960 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42729
       have i₂ := eq42594 sF2
       grind)
    | exact superpose eq42594 eq42729
    | exact resolve eq42729 eq42594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42729
  have eq43048 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq42960 eq27
    | exact resolve eq27 eq42960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq42960
  have eq43108 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq5722 eq43048
    | exact resolve eq43048 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722 eq43048
  have eq44869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42687 eq999
    | (have j0 := eq999 (M.op x y)
       grind)
    | exact resolve eq999 eq42687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq42687
  have eq44898 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq44869
  have eq44911 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq44898
       have i₂ := eq42594 (σ sF0)
       grind)
    | exact superpose eq42594 eq44898
    | exact resolve eq44898 eq42594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42594 eq44898
  have eq44933 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq44911 eq5755
    | exact resolve eq5755 eq44911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755 eq44911
  have eq45018 : False := by grind
  exact eq45018

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0 X1 x
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq69 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq25 X0 X1 (σ X2)
       grind)
    | exact superpose eq25 eq22
    | exact resolve eq22 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq103 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq89 X0 x X2
       have i₂ := eq97 x X0
       grind)
    | exact superpose eq97 eq89
    | exact resolve eq89 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq97
  have eq254 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq43
    | (have j0 := eq43 X0 X1
       have j1 := eq40 (σ (M.op X0 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq3347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq254 x y
       grind)
    | exact superpose eq254 eq16
    | (have j1 := eq254 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq254 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq254 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq254 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq3384 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3347
  have eq4210 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq3384
       grind)
    | exact superpose eq3384 eq9
    | exact resolve eq9 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq4247 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4210 x
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq4210
    | exact resolve eq4210 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4210
  have eq4248 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4247
  have eq9619 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4248
       grind)
    | exact superpose eq4248 eq10
    | exact resolve eq10 eq4248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq9662 : x = y ∨ x = y := by
    first
    | (have i₁ := eq9619
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9619
    | exact resolve eq9619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9619
  have eq9663 : x = y := by grind
  clear eq9662
  have eq14287 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9663
       grind)
    | exact superpose eq9663 eq16
    | exact resolve eq16 eq9663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9663
  have eq14288 : False := by grind
  exact eq14288

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyy_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq538 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq538 x x X2 X3
       grind)
    | (have r₁ := eq538 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq538 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq538
  have eq1197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq546 x y
       grind)
    | exact superpose eq546 eq49
    | (have j1 := eq546 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1221 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1197
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1197
    | exact resolve eq1197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1222 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1221
    | exact resolve eq1221 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1222 eq546
    | (have j0 := eq546 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq546 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq1222
  have eq1228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1226
    | exact resolve eq1226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1231 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1228
       have r₂ := eq28
       grind)
    | exact resolve eq1228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1234 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1231 eq30
    | exact resolve eq30 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1231
  have eq1252 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1234
    | exact resolve eq1234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1234
  have eq1253 : x = y := by grind
  clear eq1252
  have eq1256 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq19
    | exact resolve eq19 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1257 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq25
    | exact resolve eq25 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1253
  have eq1273 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1257
    | exact resolve eq1257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1257
  have eq1276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1273 eq27
    | exact resolve eq27 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1273
  have eq1339 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1276 eq68
    | exact resolve eq68 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1276
  have eq1367 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1339
       have i₂ := eq1256
       grind)
    | exact superpose eq1256 eq1339
    | exact resolve eq1339 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1339
  have eq1369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1367 eq15
    | exact resolve eq15 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1369
    | exact resolve eq1369 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1369
  have eq1393 : False := by grind
  exact eq1393
