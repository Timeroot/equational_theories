import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3321 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3321 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1364 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1408 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1364 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1364
    | (have j0 := eq1364 X0 X1
       grind)
    | exact resolve eq1364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq3262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq147
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq147
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq147
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq147
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq147 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq3263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3262
  have eq29155 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3263
       grind)
    | exact superpose eq3263 eq16
    | exact resolve eq16 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29169 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3263
       grind)
    | exact superpose eq3263 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3263
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3263
       grind)
    | exact resolve eq13 eq3263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq29235 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq29169
  have eq29236 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq29235
  have eq29242 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq29236
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq29236
    | exact resolve eq29236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29236
  have eq57684 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1408 y x
       have i₂ := eq29242
       grind)
    | exact superpose eq29242 eq1408
    | (have j0 := eq1408 y x
       grind)
    | exact resolve eq1408 eq29242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq29242
  have eq57769 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq57684
  have eq57812 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq57769
       have r₂ := eq29155
       grind)
    | exact resolve eq57769 eq29155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29155 eq57769
  have eq58060 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq57812
       grind)
    | exact superpose eq57812 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq57812
       grind)
    | exact resolve eq13 eq57812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58143 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq58060
  have eq58144 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58143
  have eq58405 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq155 x y
       have i₂ := eq58144
       grind)
    | exact superpose eq58144 eq155
    | (have j0 := eq155 x y
       grind)
    | exact resolve eq155 eq58144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq58144
  have eq58415 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58405
  have eq58416 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58415
  have eq59628 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq58416
       grind)
    | exact superpose eq58416 eq16
    | exact resolve eq16 eq58416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58416
  have eq60600 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59628
       have i₂ := eq57812
       grind)
    | exact superpose eq57812 eq59628
    | exact resolve eq59628 eq57812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57812 eq59628
  have eq60601 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq60600
  have eq60602 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq60601
  have eq61189 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq60602
       grind)
    | exact superpose eq60602 eq10
    | exact resolve eq10 eq60602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60602
  have eq61310 : x = y ∨ x = y := by
    first
    | (have i₁ := eq61189
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq61189
    | exact resolve eq61189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61189
  have eq61311 : x = y := by grind
  clear eq61310
  have eq62585 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61311
       grind)
    | exact superpose eq61311 eq16
    | exact resolve eq16 eq61311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61311
  have eq62586 : False := by grind
  exact eq62586

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pxy_Equation3321 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3321 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
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
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq109 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq23
    | exact resolve eq23 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq115 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq26 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq26 eq109
    | exact resolve eq109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq117 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq115
  have eq118 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq26 X0 X0 X0
       grind)
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq117
  have eq282 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq10
    | (have j1 := eq58 X0 X1
       grind)
    | exact resolve eq10 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq294 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq695 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq118 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq721 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq695 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq695
    | exact resolve eq695 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq732 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq721 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq721
    | exact resolve eq721 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq2637 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2803 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2637 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2637
    | (have j0 := eq2637 X0 X1
       grind)
    | exact resolve eq2637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq4123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq294 x y
       grind)
    | exact superpose eq294 eq16
    | (have j1 := eq294 x y
       grind)
    | exact resolve eq16 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq105150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4123
       have i₂ := eq2803 x y
       grind)
    | exact superpose eq2803 eq4123
    | (have j1 := eq2803 x y
       grind)
    | (have r₁ := eq4123
       have r₂ := eq2803 x y
       grind)
    | (have r₁ := eq4123
       have r₂ := eq2803 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4123
       have r₂ := eq2803 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4123 eq2803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803 eq4123
  have eq105153 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq105150
  have eq105154 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq105153
  have eq105189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq732 y
       have i₂ := eq105154
       grind)
    | exact superpose eq105154 eq732
    | exact resolve eq732 eq105154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq105154
  have eq105357 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq105189
       have r₂ := eq16
       grind)
    | exact resolve eq105189 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105189
  have eq105454 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq105357
       grind)
    | exact superpose eq105357 eq10
    | exact resolve eq10 eq105357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105357
  have eq105524 : x = y ∨ x = y := by
    first
    | (have i₁ := eq105454
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq105454
    | exact resolve eq105454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105454
  have eq105525 : x = y := by grind
  clear eq105524
  have eq105602 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105525
       grind)
    | exact superpose eq105525 eq16
    | exact resolve eq16 eq105525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105525
  have eq105603 : False := by grind
  exact eq105603

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation3342 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3342 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq74 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq185 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq74 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq186 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq186 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq186 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq202 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq190 (σ X0)
       grind)
    | exact superpose eq190 eq15
    | exact resolve eq15 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq202 X0
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq202
    | exact resolve eq202 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq296 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq9
    | exact resolve eq9 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq75 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq887 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq853 X0 X1 X2
       have i₂ := eq215 X0
       grind)
    | exact superpose eq215 eq853
    | (have j0 := eq853 X0 X1 X2
       grind)
    | exact resolve eq853 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq6247 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | (have j0 := eq71 X0 X0
       grind)
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq6470 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6247 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6247
    | (have j0 := eq6247 X0 X0
       grind)
    | exact resolve eq6247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq7178 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq6470 X2 X0
       grind)
    | exact superpose eq6470 eq298
    | (have j0 := eq298 X0 X1
       have j1 := eq6470 X2 X0
       grind)
    | exact resolve eq298 eq6470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq6470
  have eq7212 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq7178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178
  have eq108151 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq887 X0 X1 X2
       grind)
    | exact superpose eq887 eq10
    | (have j1 := eq887 X0 X1 X2
       grind)
    | exact resolve eq10 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq108630 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108151 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108151
    | (have j0 := eq108151 X0 X1 X2
       grind)
    | exact resolve eq108151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108151
  have eq237987 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq108630 x y X0
       grind)
    | exact superpose eq108630 eq16
    | (have j1 := eq108630 x y X0
       grind)
    | exact resolve eq16 eq108630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108630
  have eq237993 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq237987 X0
       have j1 := eq7212 y X0 X0
       grind)
    | (have r₁ := eq237987 X0
       have r₂ := eq7212 y x x
       grind)
    | exact resolve eq237987 eq7212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7212 eq237987
  have eq238048 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190 (σ y)
       have i₂ := eq237993 (σ y)
       grind)
    | exact superpose eq237993 eq190
    | (have j1 := eq237993 (σ y)
       grind)
    | exact resolve eq190 eq237993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq237993
  have eq238118 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq238048
  have eq238148 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq238118
       have i₂ := eq215 y
       grind)
    | exact superpose eq215 eq238118
    | exact resolve eq238118 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238118
  have eq238173 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq297 y X0
       have i₂ := eq238148
       grind)
    | exact superpose eq238148 eq297
    | (have j0 := eq297 y X0
       grind)
    | (have r₁ := eq297 y x
       have r₂ := eq238148
       grind)
    | exact resolve eq297 eq238148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238181 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq238148
       grind)
    | exact superpose eq238148 eq10
    | exact resolve eq10 eq238148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238148
  have eq238247 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq238173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238173
  have eq238277 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq238181
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq238181
    | exact resolve eq238181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238181
  have eq238306 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq238277
       grind)
    | exact superpose eq238277 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq238277
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq238277
       grind)
    | exact resolve eq12 eq238277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238277
  have eq238488 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq238306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238306
  have eq238839 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq238247 (σ X0)
       grind)
    | exact superpose eq238247 eq15
    | exact resolve eq15 eq238247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238247
  have eq240181 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq238839 x
       grind)
    | exact superpose eq238839 eq16
    | exact resolve eq16 eq238839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238839
  have eq240245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq240181
       have i₂ := eq238488 x
       grind)
    | exact superpose eq238488 eq240181
    | exact resolve eq240181 eq238488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238488 eq240181
  have eq240303 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq240245
  have eq240304 : x = (M.op x x) := by grind
  clear eq240303
  have eq240315 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq9
    | exact resolve eq9 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240316 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq240304
       grind)
    | exact resolve eq12 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240336 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq296 x X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq296
    | exact resolve eq296 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq240337 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq297 x X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq297
    | (have j0 := eq297 x X0
       grind)
    | exact resolve eq297 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq240588 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq240337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240337
  have eq240590 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq240316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240316
  have eq240642 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq240336 X0
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq240336
    | exact resolve eq240336 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq240336
  have eq240650 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq240315 X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq240315
    | exact resolve eq240315 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240315
  have eq240657 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq240642 X0
       have i₂ := eq240304
       grind)
    | exact superpose eq240304 eq240642
    | exact resolve eq240642 eq240304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240304 eq240642
  have eq241104 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq240590 (τ X0)
       grind)
    | exact superpose eq240590 eq18
    | exact resolve eq18 eq240590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq241194 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq241104 X0
       have i₂ := eq240650 (τ X0)
       grind)
    | exact superpose eq240650 eq241104
    | exact resolve eq241104 eq240650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240650 eq241104
  have eq241272 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq241194 X0
       have i₂ := eq240588 X0
       grind)
    | exact superpose eq240588 eq241194
    | exact resolve eq241194 eq240588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241194
  have eq243272 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq240588 (σ X0)
       grind)
    | exact superpose eq240588 eq15
    | exact resolve eq15 eq240588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240588
  have eq243473 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq243272 X0
       have i₂ := eq240590 X0
       grind)
    | exact superpose eq240590 eq243272
    | exact resolve eq243272 eq240590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240590 eq243272
  have eq245699 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq241272 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq241272
    | exact resolve eq241272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241272
  have eq247423 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq240657 (σ X0)
       have i₂ := eq243473 X0
       grind)
    | exact superpose eq243473 eq240657
    | exact resolve eq240657 eq243473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240657
  have eq250131 : ∀ X0 : G, (σ (M.op X0 x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq243473 X0
       have i₂ := eq245699 X0
       grind)
    | exact superpose eq245699 eq243473
    | exact resolve eq243473 eq245699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243473 eq245699
  have eq252602 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq247423 y
       grind)
    | exact superpose eq247423 eq16
    | exact resolve eq16 eq247423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247423
  have eq252787 : False := by grind
  exact eq252787

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3342 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3342 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq46 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq368 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq399 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq760 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq84
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq84
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq84
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq84
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq761 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq760
  have eq6181 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq761
       grind)
    | exact superpose eq761 eq16
    | exact resolve eq16 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6182 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq761
       grind)
    | exact superpose eq761 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq761
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq761
       grind)
    | exact resolve eq13 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq6183 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6182
  have eq6184 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6183
  have eq6186 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6184
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6184
    | exact resolve eq6184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184
  have eq9696 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq399 x y
       have i₂ := eq6186
       grind)
    | exact superpose eq6186 eq399
    | (have j0 := eq399 x y
       grind)
    | exact resolve eq399 eq6186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq9698 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq6186
       grind)
    | exact superpose eq6186 eq10
    | exact resolve eq10 eq6186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6186
  have eq9742 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq9696
  have eq9770 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9698
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9698
    | exact resolve eq9698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9698
  have eq9771 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9742
       have r₂ := eq6181
       grind)
    | exact resolve eq9742 eq6181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181 eq9742
  have eq9774 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq9770
       have r₂ := eq13 y x
       grind)
    | exact resolve eq9770 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq10134 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq9774
       grind)
    | exact superpose eq9774 eq86
    | (have j0 := eq86 x y
       grind)
    | exact resolve eq86 eq9774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq9774
  have eq10137 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10134
  have eq10138 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10137
  have eq10299 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq10138
       grind)
    | exact superpose eq10138 eq16
    | exact resolve eq16 eq10138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10138
  have eq10502 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10299
       have i₂ := eq9771
       grind)
    | exact superpose eq9771 eq10299
    | exact resolve eq10299 eq9771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq10299
  have eq10503 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10502
  have eq10504 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10503
  have eq10712 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10504
       grind)
    | exact superpose eq10504 eq10
    | exact resolve eq10 eq10504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10504
  have eq10792 : x = y ∨ x = y := by
    first
    | (have i₁ := eq10712
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10712
    | exact resolve eq10712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10712
  have eq10793 : x = y := by grind
  clear eq10792
  have eq10959 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10793
       grind)
    | exact superpose eq10793 eq16
    | exact resolve eq16 eq10793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10793
  have eq10960 : False := by grind
  exact eq10960

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation3343 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3343 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq67
    | exact resolve eq67 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq74
    | exact resolve eq74 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq74
  have eq240 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq56 X1 X0
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq10
    | (have j1 := eq56 X1 X0
       grind)
    | exact resolve eq10 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq253 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | exact resolve eq240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1734 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1847 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1734 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1734
    | (have j0 := eq1734 X0 X1
       grind)
    | exact resolve eq1734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq2516 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq253 y x
       grind)
    | exact superpose eq253 eq16
    | (have j1 := eq253 y x
       grind)
    | exact resolve eq16 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq14097 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2516
       have i₂ := eq1847 y x
       grind)
    | exact superpose eq1847 eq2516
    | (have j1 := eq1847 y x
       grind)
    | (have r₁ := eq2516
       have r₂ := eq1847 y x
       grind)
    | (have r₁ := eq2516
       have r₂ := eq1847 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2516
       have r₂ := eq1847 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2516 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847 eq2516
  have eq14102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14097
  have eq14103 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14102
  have eq14882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq14103
       grind)
    | exact superpose eq14103 eq75
    | exact resolve eq75 eq14103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq14103
  have eq14940 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14882
       have r₂ := eq16
       grind)
    | exact resolve eq14882 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14882
  have eq15780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14940
       grind)
    | exact superpose eq14940 eq10
    | exact resolve eq10 eq14940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14940
  have eq15852 : x = y ∨ x = y := by
    first
    | (have i₁ := eq15780
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15780
    | exact resolve eq15780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15780
  have eq15853 : x = y := by grind
  clear eq15852
  have eq17013 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15853
       grind)
    | exact superpose eq15853 eq16
    | exact resolve eq16 eq15853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15853
  have eq17014 : False := by grind
  exact eq17014

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3352 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq75 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq288 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq288
    | (have j0 := eq288 X0 X1
       grind)
    | exact resolve eq288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq75
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq75
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq75
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq764
  have eq4049 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq16
    | exact resolve eq16 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4050 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq765
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq765
       grind)
    | exact resolve eq13 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq4051 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4050
  have eq4052 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4051
  have eq4054 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4052
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4052
    | exact resolve eq4052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq6721 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq317 x y
       have i₂ := eq4054
       grind)
    | exact superpose eq4054 eq317
    | (have j0 := eq317 x y
       grind)
    | exact resolve eq317 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq6723 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4054
       grind)
    | exact superpose eq4054 eq10
    | exact resolve eq10 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4054
  have eq6761 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6721
  have eq6789 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6723
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6723
    | exact resolve eq6723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6790 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6761
       have r₂ := eq4049
       grind)
    | exact resolve eq6761 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049 eq6761
  have eq6793 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq6789
       have r₂ := eq13 y x
       grind)
    | exact resolve eq6789 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq7147 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77 x y
       have i₂ := eq6793
       grind)
    | exact superpose eq6793 eq77
    | (have j0 := eq77 x y
       grind)
    | exact resolve eq77 eq6793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq6793
  have eq7150 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7147
  have eq7151 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7150
  have eq7311 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7151
       grind)
    | exact superpose eq7151 eq16
    | exact resolve eq16 eq7151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151
  have eq7511 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7311
       have i₂ := eq6790
       grind)
    | exact superpose eq6790 eq7311
    | exact resolve eq7311 eq6790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790 eq7311
  have eq7512 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7511
  have eq7513 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7512
  have eq7719 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7513
       grind)
    | exact superpose eq7513 eq10
    | exact resolve eq10 eq7513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7513
  have eq7793 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7719
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7719
    | exact resolve eq7719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7719
  have eq7794 : x = y := by grind
  clear eq7793
  have eq7919 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7794
       grind)
    | exact superpose eq7794 eq16
    | exact resolve eq16 eq7794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7794
  have eq7920 : False := by grind
  exact eq7920

/-- `Equation3474`: `x ◇ x = y ◇ ((x ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation3474 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3474 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3474.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ X1 = X2 ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq71 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq91 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq200 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq60 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq10
    | (have j1 := eq60 X0 X1
       grind)
    | exact resolve eq10 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq729 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq730 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq824 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq825 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq824 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq1093 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq730 (σ X0) (σ X1)
       grind)
    | exact superpose eq730 eq15
    | (have j1 := eq730 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq1126 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1093
    | (have j0 := eq1093 X0 X1
       grind)
    | exact resolve eq1093 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1257 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq825 X0 (τ X1)
       grind)
    | exact superpose eq825 eq19
    | (have j1 := eq825 X0 (τ X1)
       grind)
    | exact resolve eq19 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2598 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211 x y
       grind)
    | exact superpose eq211 eq16
    | (have j1 := eq211 x y
       grind)
    | exact resolve eq16 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq2925 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3007 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ X2) = X1 ∨ (M.op (σ X2) X1) = (k (σ X2) X1) ∨ (k (σ X2) X0) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2 X1
       have i₂ := eq49 X0 X2
       grind)
    | (have i₁ := eq71 (τ X0) X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq71
    | (have j0 := eq71 X2 X1
       have j1 := eq49 X0 X2
       grind)
    | exact resolve eq71 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq71
  have eq3112 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (σ X2) = X1 ∨ (M.op (σ X2) X1) = (k (σ X2) X1) ∨ (k (σ X2) X0) = (σ (M.op (τ X0) X2)) ∨ (τ X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3007 X0 X1 X2
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq3007
    | (have j0 := eq3007 X0 X1 X2
       grind)
    | (have r₁ := eq3007 X0 X0 X2
       have r₂ := eq31 X0
       grind)
    | exact resolve eq3007 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3007
  have eq3182 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2925 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2925
    | (have j0 := eq2925 X0 X1
       grind)
    | exact resolve eq2925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq18370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2598
       have i₂ := eq3182 x y
       grind)
    | exact superpose eq3182 eq2598
    | (have j1 := eq3182 x y
       grind)
    | (have r₁ := eq2598
       have r₂ := eq3182 x y
       grind)
    | (have r₁ := eq2598
       have r₂ := eq3182 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2598
       have r₂ := eq3182 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2598 eq3182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598 eq3182
  have eq18371 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18370
  have eq18372 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18371
  have eq19073 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq18372
       grind)
    | exact superpose eq18372 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18372
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18372
       grind)
    | exact resolve eq13 eq18372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18372
  have eq61896 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1257 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1257
    | exact resolve eq1257 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq61920 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61896 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61896
    | (have j0 := eq61896 X0 X1
       grind)
    | exact resolve eq61896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61896
  have eq134351 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134352 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq135553 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134351 (τ X1) (τ X0)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq134351
    | (have j0 := eq134351 (τ X1) (τ X0)
       grind)
    | exact resolve eq134351 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134351
  have eq135559 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135553 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq135553
    | (have j0 := eq135553 X0 X1
       grind)
    | exact resolve eq135553 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135553
  have eq135567 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135559 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq135559
    | (have j0 := eq135559 X0 X1
       grind)
    | exact resolve eq135559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135559
  have eq135574 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135567 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq135567
    | (have j0 := eq135567 X0 X1
       grind)
    | (have r₁ := eq135567 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq135567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135567
  have eq135580 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = (σ (k (τ X1) (τ X0))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135574 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135574
    | (have j0 := eq135574 X0 X1
       grind)
    | exact resolve eq135574 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135574
  have eq135582 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135580 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq135580
    | (have j0 := eq135580 X0 X1
       grind)
    | exact resolve eq135580 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135580
  have eq135584 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135582 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135582
    | (have j0 := eq135582 X0 X1
       grind)
    | exact resolve eq135582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135582
  have eq135586 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135584 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq135584
    | (have j0 := eq135584 X0 X1
       grind)
    | exact resolve eq135584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135584
  have eq135588 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq135586 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135586
    | (have j0 := eq135586 X0 X1
       grind)
    | exact resolve eq135586 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135586
  have eq135676 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq135588 X1 X0
       have i₂ := eq825 X0 X1
       grind)
    | exact superpose eq825 eq135588
    | (have j0 := eq135588 X0 X1
       have j1 := eq825 X1 X0
       grind)
    | (have r₁ := eq135588 X0 X1
       have r₂ := eq825 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq135588 X0 X1
       have r₂ := eq825 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq135588 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135588
  have eq135712 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135676
  have eq135738 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135712 X0 X1
       have j1 := eq1271 X1 X0
       grind)
    | (have r₁ := eq135712 X0 X1
       have r₂ := eq1271 X0 X1
       grind)
    | (have r₁ := eq135712 X0 X1
       have r₂ := eq1271 (M.op X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq135712 X0 X1
       have r₂ := eq1271 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq135712 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq135712
  have eq136035 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134352 (τ X0) (τ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq134352
    | (have j0 := eq134352 (τ X0) (τ X1)
       grind)
    | exact resolve eq134352 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq136041 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136035 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq136035
    | (have j0 := eq136035 X0 X1
       grind)
    | exact resolve eq136035 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq136035
  have eq136049 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136041 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq136041
    | (have j0 := eq136041 X0 X1
       grind)
    | exact resolve eq136041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136041
  have eq136056 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136049 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq136049
    | (have j0 := eq136049 X0 X1
       grind)
    | (have r₁ := eq136049 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq136049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136049
  have eq136060 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136056 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136056
    | (have j0 := eq136056 X0 X1
       grind)
    | exact resolve eq136056 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136056
  have eq136064 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136060 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq136060
    | (have j0 := eq136060 X0 X1
       grind)
    | exact resolve eq136060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136060
  have eq136066 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136064 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq136064
    | (have j0 := eq136064 X0 X1
       grind)
    | exact resolve eq136064 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136064
  have eq136068 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq136066 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq136066
    | (have j0 := eq136066 X0 X1
       grind)
    | exact resolve eq136066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136066
  have eq136070 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136068 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136068
    | (have j0 := eq136068 X0 X1
       grind)
    | exact resolve eq136068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136068
  have eq136135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136070 X0 X1
       have i₂ := eq825 X0 X1
       grind)
    | exact superpose eq825 eq136070
    | (have j0 := eq136070 X0 X1
       have j1 := eq825 X0 X1
       grind)
    | (have r₁ := eq136070 X0 X1
       have r₂ := eq825 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq136070 X0 X1
       have r₂ := eq825 (k X1 X0) (k X0 X1)
       grind)
    | exact resolve eq136070 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq136070
  have eq136183 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136135
  have eq136189 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136183 X0 X1
       have j1 := eq1272 X0 X1
       grind)
    | (have r₁ := eq136183 X1 X0
       have r₂ := eq1272 X0 X1
       grind)
    | (have r₁ := eq136183 X0 X1
       have r₂ := eq1272 (M.op X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq136183 X0 X1
       have r₂ := eq1272 (k X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq136183 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq136183
  have eq141390 : x = y ∨ (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq19073 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19073
  have eq141391 : (k y x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq141390
  have eq141466 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq135738 y x
       have i₂ := eq141391
       grind)
    | exact superpose eq141391 eq135738
    | (have j0 := eq135738 x y
       grind)
    | (have r₁ := eq135738 y x
       have r₂ := eq141391
       grind)
    | exact resolve eq135738 eq141391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135738 eq141391
  have eq141477 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq141466
  have eq141478 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq141477
  have eq154729 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3112 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq164504 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq154729 X0 X1
       grind)
    | exact superpose eq154729 eq10
    | (have j1 := eq154729 X0 X1
       grind)
    | exact resolve eq10 eq154729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154729
  have eq164513 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164504 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq164504
    | (have j0 := eq164504 X0 X1
       grind)
    | exact resolve eq164504 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq164504
  have eq164527 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 (τ (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq164513 X0 (σ X1)
       grind)
    | exact superpose eq164513 eq15
    | (have j1 := eq164513 X0 (σ X1)
       grind)
    | exact resolve eq15 eq164513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164513
  have eq164528 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164527 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164527
    | (have j0 := eq164527 X0 X1
       grind)
    | exact resolve eq164527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164527
  have eq164531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq164528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq164528
    | (have j0 := eq164528 X0 X1
       grind)
    | exact resolve eq164528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164528
  have eq164547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op y x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164531 x y
       grind)
    | exact superpose eq164531 eq16
    | (have j1 := eq164531 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq164531 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq164531 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq164531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164531
  have eq164550 : (M.op y x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq61920 y x
       grind)
    | (have r₁ := eq164547
       have r₂ := eq61920 y x
       grind)
    | (have r₁ := eq164547
       have r₂ := eq61920 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq164547
       have r₂ := eq61920 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq164547 eq61920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61920 eq164547
  have eq164579 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq136189 y x
       have i₂ := eq164550
       grind)
    | exact superpose eq164550 eq136189
    | (have j0 := eq136189 x y
       grind)
    | (have r₁ := eq136189 y x
       have r₂ := eq164550
       grind)
    | exact resolve eq136189 eq164550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136189 eq164550
  have eq164582 : (M.op y x) ≠ (M.op y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq164579
  have eq164583 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq164582
  have eq164640 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq134352 x y
       have i₂ := eq164583
       grind)
    | exact superpose eq164583 eq134352
    | (have j0 := eq134352 x y
       grind)
    | exact resolve eq134352 eq164583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134352 eq164583
  have eq164660 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq164640
  have eq164694 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq164660
       have r₂ := eq16
       grind)
    | exact resolve eq164660 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164660
  have eq164945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq164694
       have i₂ := eq141478
       grind)
    | exact superpose eq141478 eq164694
    | exact resolve eq164694 eq141478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141478 eq164694
  have eq164964 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq164945
  have eq164965 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq164964
  have eq164972 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq164965
       grind)
    | exact superpose eq164965 eq10
    | exact resolve eq10 eq164965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164965
  have eq165413 : x = y ∨ x = y := by
    first
    | (have i₁ := eq164972
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164972
    | exact resolve eq164972 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164972
  have eq165414 : x = y := by grind
  clear eq165413
  have eq165416 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq165414
       grind)
    | exact superpose eq165414 eq16
    | exact resolve eq16 eq165414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165414
  have eq165417 : False := by grind
  exact eq165417

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pyx_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq26 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq26 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq27 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq36 X0
       have i₂ := eq27 (M.op X0 X0) x
       grind)
    | exact superpose eq27 eq36
    | exact resolve eq36 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq93 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq83
  have eq1107 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq10
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq10 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq2542 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1197 (M.op X0 X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq1197
    | (have j0 := eq1197 (M.op X0 X0)
       grind)
    | exact resolve eq1197 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1197
  have eq2552 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq3137 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ (M.op X0 X0)) x
       have i₂ := eq2552 X0
       grind)
    | exact superpose eq2552 eq27
    | exact resolve eq27 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq14993 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq428 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq14995 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14993 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14993
  have eq14996 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq15188 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq14996 (σ X0)
       grind)
    | exact superpose eq14996 eq15
    | exact resolve eq15 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15213 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15188 X0
       have i₂ := eq14996 X0
       grind)
    | exact superpose eq14996 eq15188
    | exact resolve eq15188 eq14996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14996 eq15188
  have eq16073 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq16225 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16073 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq16073
    | exact resolve eq16073 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16073
  have eq16262 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq16225
  have eq18508 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq19241 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18508 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18508
    | (have j0 := eq18508 X0 X1
       grind)
    | exact resolve eq18508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq93891 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1107 X1 X0
       grind)
    | exact superpose eq1107 eq10
    | (have j1 := eq1107 X1 X0
       grind)
    | exact resolve eq10 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq94554 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93891 X0 X1
       have i₂ := eq15213 X0
       grind)
    | exact superpose eq15213 eq93891
    | (have j0 := eq93891 X0 X1
       grind)
    | exact resolve eq93891 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93891
  have eq95331 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94554 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq94554
    | (have j0 := eq94554 X0 X1
       grind)
    | exact resolve eq94554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94554
  have eq95954 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95331 X0 X1
       have i₂ := eq15213 X1
       grind)
    | exact superpose eq15213 eq95331
    | (have j0 := eq95331 X0 X1
       grind)
    | exact resolve eq95331 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15213 eq95331
  have eq96395 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95954 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq95954
    | (have j0 := eq95954 X0 X1
       grind)
    | exact resolve eq95954 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95954
  have eq1326822 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96395 y x
       grind)
    | exact superpose eq96395 eq16
    | (have j1 := eq96395 y x
       grind)
    | exact resolve eq16 eq96395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96395
  have eq1326831 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq19241 x y
       grind)
    | (have r₁ := eq1326822
       have r₂ := eq19241 x y
       grind)
    | exact resolve eq1326822 eq19241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19241 eq1326822
  have eq1326903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16262 y
       have i₂ := eq1326831
       grind)
    | exact superpose eq1326831 eq16262
    | exact resolve eq16262 eq1326831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16262 eq1326831
  have eq1327196 : y = (M.op x x) := by
    first
    | (have r₁ := eq1326903
       have r₂ := eq16
       grind)
    | exact resolve eq1326903 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326903
  have eq1327249 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq27 x x
       have i₂ := eq1327196
       grind)
    | exact superpose eq1327196 eq27
    | exact resolve eq27 eq1327196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1327271 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3137 x x
       have i₂ := eq1327196
       grind)
    | exact superpose eq1327196 eq3137
    | exact resolve eq3137 eq1327196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137 eq1327196
  have eq1329246 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1327271 (σ x)
       grind)
    | exact superpose eq1327271 eq16
    | exact resolve eq16 eq1327271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327271
  have eq1329295 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1329246
       have i₂ := eq1327249 x
       grind)
    | exact superpose eq1327249 eq1329246
    | exact resolve eq1329246 eq1327249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327249 eq1329246
  have eq1329296 : False := by grind
  exact eq1329296
