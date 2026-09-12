import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyy_pxy_y_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = b :=
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
  have eq3753 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq3772 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3753
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3753
    | exact resolve eq3753 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753
  have eq3774 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3772
    | exact resolve eq3772 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772
  have eq3781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3774 eq308
    | (have j0 := eq308 x (σ y)
       grind)
    | exact resolve eq308 eq3774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq3774
  have eq3790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq3781
    | exact resolve eq3781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3781
  have eq3801 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq3790
       have r₂ := eq27
       grind)
    | exact resolve eq3790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq3811 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3801 eq126
    | exact resolve eq126 eq3801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq3801
  have eq3845 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq3811
    | exact resolve eq3811 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3811
  have eq3846 : y = (M.op y y) := by grind
  clear eq3845
  have eq3849 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3846
       have i₂ := eq294 y X0
       grind)
    | (have i₁ := eq3846
       have i₂ := eq294 X0 y
       grind)
    | exact superpose eq294 eq3846
    | exact resolve eq3846 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq3846
  have eq3993 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq3849 (M.op x x)
       grind)
    | exact superpose eq3849 eq14
    | exact resolve eq14 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4013 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq435 sF0
       have i₂ := eq3849 sF0
       grind)
    | exact superpose eq3849 eq435
    | exact resolve eq435 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq4024 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq3849 sF0
       grind)
    | exact superpose eq3849 eq140
    | exact resolve eq140 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq4038 : y = (σ y) := by
    first
    | (have i₁ := eq4024
       have i₂ := eq3849 sF1
       grind)
    | exact superpose eq3849 eq4024
    | exact resolve eq4024 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4047 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4013
       have i₂ := eq3849 sF1
       grind)
    | exact superpose eq3849 eq4013
    | exact resolve eq4013 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849 eq4013
  have eq4095 : y = (σ y) := by
    first
    | (have i₁ := eq4038
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4038
    | exact resolve eq4038 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4038
  have eq4100 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4047
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4047
    | exact resolve eq4047 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4047
  have eq4106 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq4100
    | exact resolve eq4100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4100
  have eq4136 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq4095 eq26
    | exact resolve eq26 eq4095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4095
  have eq4419 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4136
       have i₂ := eq3993 sF2
       grind)
    | exact superpose eq3993 eq4136
    | exact resolve eq4136 eq3993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3993 eq4136
  have eq4421 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4419 eq27
    | exact resolve eq27 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4419
  have eq4430 : False := by grind
  exact eq4430

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_y_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x X0
       have i₂ := eq64 x X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq64 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq64 X0 X2
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq79 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 X1 X2
       have i₂ := eq63 X0 X0 X1
       grind)
    | exact superpose eq63 eq74
    | exact resolve eq74 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq74
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 X1 X2
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq73
    | (have j0 := eq73 X0 X1 X2
       grind)
    | (have r₁ := eq73 X0 (M.op X0 X0) X2
       have r₂ := eq76 X0 X0
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 X0 X1 X2 X3
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq72
    | exact resolve eq72 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq165 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X3 X2
       have i₂ := eq79 X1 X2 X0
       grind)
    | (have i₁ := eq76 X0 (M.op X0 X0)
       have i₂ := eq79 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq79 eq76
    | exact resolve eq76 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq79
  have eq197 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq205 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq197 (σ X1) X0
       grind)
    | exact superpose eq197 eq28
    | exact resolve eq28 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq206 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 X0)
       have i₂ := eq197 (τ X1) X0
       grind)
    | exact superpose eq197 eq17
    | exact resolve eq17 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq302 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq71 X0 X0
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq751 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 X2
       have i₂ := eq312 X2 X0
       grind)
    | exact superpose eq312 eq71
    | (have j1 := eq312 X1 X0
       grind)
    | exact resolve eq71 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X1 (σ (M.op X1 X1))
       have i₂ := eq312 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq312 eq206
    | (have j1 := eq312 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq206 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq788 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X1 (τ (M.op X1 X1))
       have i₂ := eq312 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq312 eq205
    | (have j1 := eq312 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq205 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq790 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq791 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq917 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq791 X2 (M.op x x)
       have i₂ := eq165 (M.op x x) x X0 X1
       grind)
    | (have i₁ := eq791 X2 (M.op x x)
       have i₂ := eq165 X0 X1 (M.op x x) x
       grind)
    | exact superpose eq165 eq791
    | exact resolve eq791 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 x) X1 x
       have i₂ := eq791 (M.op X1 x) X1
       grind)
    | exact superpose eq791 eq9
    | exact resolve eq9 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1481 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq71 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq71
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq71 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1524 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
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
  have eq1538 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1539 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1538 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq2028 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165 X2 X3 (M.op x x) x
       have i₂ := eq917 X0 X1 (M.op x x)
       grind)
    | exact superpose eq917 eq165
    | exact resolve eq165 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq7800 : ∀ X0 X2 X3 : G, (k X2 X0) = X0 ∨ (M.op X3 X3) = (k X0 X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq197 X0 X2
       have i₂ := eq751 X0 x X2
       grind)
    | (have i₁ := eq197 X0 x
       have i₂ := eq751 (M.op x x) x X2
       grind)
    | exact superpose eq751 eq197
    | (have j1 := eq751 X0 X3 X2
       grind)
    | exact resolve eq197 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq751
  have eq8541 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7800 X0 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7800
  have eq8549 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq8541 X0 X1
       have j1 := eq312 X1 X0
       grind)
    | (have r₁ := eq8541 (k X1 X1) X0
       have r₂ := eq312 X0 X1
       grind)
    | (have r₁ := eq8541 X1 X0
       have r₂ := eq312 X0 X1
       grind)
    | (have r₁ := eq8541 (M.op X0 X0) X1
       have r₂ := eq312 X0 (M.op X1 X1)
       grind)
    | exact resolve eq8541 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq8541
  have eq8723 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165 X1 X2 (M.op x x) x
       have i₂ := eq8549 X0 (M.op x x)
       grind)
    | exact superpose eq8549 eq165
    | exact resolve eq165 eq8549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq8736 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X1 (σ (M.op X1 X1))
       have i₂ := eq8549 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq8549 eq951
    | exact resolve eq951 eq8549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq8549
  have eq8920 : ∀ X0 X1 X2 X4 : G, (σ (M.op X0 (M.op X1 (M.op X0 X2)))) = (k X4 X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8736 X4 x
       have i₂ := eq81 x X1 X0 X2
       grind)
    | exact superpose eq81 eq8736
    | exact resolve eq8736 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq8736
  have eq14819 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1539 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq14871 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14819 X0 X1
       have j1 := eq1481 X0 X1 x
       grind)
    | (have r₁ := eq14819 x x
       have r₂ := eq1481 x x x
       grind)
    | (have r₁ := eq14819 X0 X1
       have r₂ := eq1481 X0 X1 X1
       grind)
    | exact resolve eq14819 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq14819
  have eq32585 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 X0
       have i₂ := eq14871 X2 X0
       grind)
    | exact superpose eq14871 eq71
    | (have j1 := eq14871 X2 X0
       grind)
    | exact resolve eq71 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq32605 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq790 X1 X0
       have i₂ := eq14871 X2 X0
       grind)
    | exact superpose eq14871 eq790
    | (have j1 := eq14871 X2 X0
       grind)
    | exact resolve eq790 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq32607 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq791 X1 X0
       have i₂ := eq14871 X2 X0
       grind)
    | exact superpose eq14871 eq791
    | (have j1 := eq14871 X2 X0
       grind)
    | exact resolve eq791 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq32719 : ∀ X0 X1 X2 X3 : G, (k X2 X2) = (M.op X1 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8723 X2 X1 X0
       have i₂ := eq14871 X3 X0
       grind)
    | exact superpose eq14871 eq8723
    | (have j1 := eq14871 X3 X0
       grind)
    | exact resolve eq8723 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8723 eq14871
  have eq33051 : ∀ X0 X1 X3 : G, (M.op X1 X0) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X1 x) X1 x
       have i₂ := eq32585 X0 (M.op X1 x) x
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq32585 (M.op X0 (M.op X1 x)) X1 x
       grind)
    | exact superpose eq32585 eq9
    | (have j1 := eq32585 X0 X1 X3
       grind)
    | exact resolve eq9 eq32585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32585
  have eq49226 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X2)) = (σ (M.op X3 X0)) ∨ (M.op X4 X0) = (k X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2028 X3 X0 X1 X2
       have i₂ := eq33051 X0 X0 X4
       grind)
    | exact superpose eq33051 eq2028
    | (have j1 := eq33051 X0 X1 X4
       grind)
    | exact resolve eq2028 eq33051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq33051
  have eq122041 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X1 ∨ (k X2 (σ X1)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32605 (σ X1) X0 X2
       grind)
    | exact superpose eq32605 eq10
    | (have j1 := eq32605 (σ X1) X1 X2
       grind)
    | exact resolve eq10 eq32605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32605
  have eq124347 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) (M.op X0 X0)) ∨ (k X1 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq32607 y X0 X1
       grind)
    | exact superpose eq32607 eq16
    | (have j1 := eq32607 y X1 X1
       grind)
    | exact resolve eq16 eq32607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32607
  have eq125136 : ∀ X1 : G, (k X1 y) = (M.op X1 y) := by
    intro X1
    first
    | (have j0 := eq124347 x X1
       have j1 := eq49226 y X1 x x X1
       grind)
    | (have r₁ := eq124347 x X1
       have r₂ := eq49226 y (σ x) x x x
       grind)
    | exact resolve eq124347 eq49226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49226 eq124347
  have eq514511 : ∀ X0 X1 X3 X4 : G, (k X3 X3) = (σ (M.op X1 X0)) ∨ (M.op X4 (σ X0)) = (k X4 (σ X0)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8920 X1 (M.op X1 x) x X3
       have i₂ := eq122041 (M.op X1 x) X0 X4
       grind)
    | (have i₁ := eq8920 X0 X1 x X4
       have i₂ := eq122041 X0 (M.op X1 (M.op X0 x)) x
       grind)
    | exact superpose eq122041 eq8920
    | (have j1 := eq122041 X0 X0 X4
       grind)
    | exact resolve eq8920 eq122041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8920 eq122041
  have eq622338 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (k X0 X0) ∨ (k X1 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq32719 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32719 eq16
    | (have j1 := eq32719 (σ y) X1 x X1
       grind)
    | exact resolve eq16 eq32719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32719
  have eq622657 : ∀ X1 : G, (k X1 (σ y)) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have j0 := eq622338 x X1
       have j1 := eq514511 y X1 x X1
       grind)
    | (have r₁ := eq622338 x X1
       have r₂ := eq514511 y x x x
       grind)
    | exact resolve eq622338 eq514511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514511 eq622338
  have eq624020 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq622657 (σ X0)
       grind)
    | exact superpose eq622657 eq15
    | exact resolve eq15 eq622657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622657
  have eq624163 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq624020 X0
       have i₂ := eq125136 X0
       grind)
    | exact superpose eq125136 eq624020
    | exact resolve eq624020 eq125136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125136 eq624020
  have eq624311 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq624163 x
       grind)
    | exact superpose eq624163 eq16
    | (have r₁ := eq16
       have r₂ := eq624163 x
       grind)
    | exact resolve eq16 eq624163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624163
  have eq624312 : False := by grind
  exact eq624312

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
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
  have eq76 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq241 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq249 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq409 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) (M.op x y))) = (M.op X1 (M.op x (M.op (M.op X0 X0) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) x
       have i₂ := eq51 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq459 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X1 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq249
    | exact resolve eq249 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq409 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq537 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq524 X0
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 x (M.op x y)
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 (M.op x y) x
       grind)
    | exact resolve eq524 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq554 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq410 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq567 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq554 X0
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq554 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1115 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq66 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq53 x X1 x X0
       grind)
    | exact superpose eq53 eq66
    | (have j0 := eq66 X0 X1 x X4
       grind)
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq1142 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1115 X0 X1 X4
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1115
    | (have j0 := eq1115 X0 X1 X4
       grind)
    | (have r₁ := eq1115 X0 (M.op X0 X0) X4
       have r₂ := eq249 X0 X0
       grind)
    | exact resolve eq1115 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1315 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0
       have i₂ := eq55 X0 (σ X0)
       grind)
    | exact superpose eq55 eq95
    | exact resolve eq95 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1322 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq51
    | (have j1 := eq95 X0 X0
       grind)
    | exact resolve eq51 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1365 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1367 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1374 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1382 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1367 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1367 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1383 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1374
    | (have j0 := eq1374 X0 X1
       grind)
    | exact resolve eq1374 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1400 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1383 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1383
    | (have j0 := eq1383 X0 X1
       grind)
    | exact resolve eq1383 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1383
  have eq1540 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq537 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq537
    | exact resolve eq537 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1634 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq567
    | exact resolve eq567 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1639 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq567 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq567
    | exact resolve eq567 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1947 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1540 eq34
    | exact resolve eq34 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq2035 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1639 eq34
    | exact resolve eq34 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq7166 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1400 X0 (τ X1)
       grind)
    | exact superpose eq1400 eq34
    | (have j1 := eq1400 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1400
  have eq7195 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7166 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7166
    | (have j0 := eq7166 X0 X1
       grind)
    | exact resolve eq7166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq7271 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7195 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7195
    | (have j0 := eq7195 X0 X1
       grind)
    | exact resolve eq7195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7195
  have eq8073 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq1947 eq1947
    | exact resolve eq1947 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq10060 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq567 eq1382
    | (have j0 := eq1382 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1382 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq10082 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq10060 X0
       grind)
    | (have r₁ := eq10060 X0
       have r₂ := eq8073 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq10060 X0
       have r₂ := eq8073 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq10060 eq8073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073 eq10060
  have eq10110 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10082 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq10082 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq10082
    | exact resolve eq10082 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10150 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq2035 eq10082
    | exact resolve eq10082 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq10269 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10082 eq36
    | exact resolve eq36 eq10082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq10082
  have eq10296 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq567 eq10269
    | exact resolve eq10269 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq10269
  have eq10383 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10296
       grind)
    | exact superpose eq10296 eq16
    | exact resolve eq16 eq10296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10296
  have eq10688 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq10150 X0 (M.op X1 x)
       grind)
    | exact superpose eq10150 eq14
    | exact resolve eq14 eq10150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13626 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq10110 eq10
    | exact resolve eq10 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13645 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq10110 eq381
    | exact resolve eq381 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq10110
  have eq13648 : ∀ X0 X1 : G, (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13645 X0 X1
       have i₂ := eq16 (M.op sF4 sF4)
       grind)
    | exact superpose eq16 eq13645
    | exact resolve eq13645 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13645
  have eq13659 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1634 eq13626
    | exact resolve eq13626 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13626
  have eq13718 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1634 eq13648
    | exact resolve eq13648 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634 eq13648
  have eq14647 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (τ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq459 eq13718
    | exact resolve eq13718 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq14742 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (M.op X2 (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | exact superpose eq13718 eq415
    | exact resolve eq415 eq13718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq13718
  have eq19012 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1365 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1365
    | (have j0 := eq1365 y
       grind)
    | exact resolve eq1365 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19013 : (σ (k (M.op x y) (M.op x y))) = (M.op x (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1365
    | (have j0 := eq1365 (M.op x y)
       grind)
    | exact resolve eq1365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq19134 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51 eq19013
    | exact resolve eq19013 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013
  have eq19135 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq51 eq19012
    | exact resolve eq19012 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012
  have eq19155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq19134
    | exact resolve eq19134 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq19134
  have eq19156 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19135
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq19135
    | exact resolve eq19135 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq19135
  have eq19164 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq1142 x (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq19155
       have r₂ := eq1142 (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | (have r₁ := eq19155
       have r₂ := eq1142 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq19155 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155
  have eq19165 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq1142 x (σ y) (σ y)
       grind)
    | (have r₁ := eq19156
       have r₂ := eq1142 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq19156
       have r₂ := eq1142 (σ y) (σ y) x
       grind)
    | exact resolve eq19156 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq19156
  have eq50228 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271
  have eq50472 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19164 eq50228
    | (have j0 := eq50228 X0 (σ (M.op x y))
       grind)
    | exact resolve eq50228 eq19164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19164
  have eq50474 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq19165 eq50228
    | (have j0 := eq50228 X0 (σ y)
       grind)
    | exact resolve eq50228 eq19165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19165 eq50228
  have eq50482 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq50472 X0
       have i₂ := eq241 sF1 X1
       grind)
    | (have i₁ := eq50472 X0
       have i₂ := eq241 X0 sF1
       grind)
    | exact superpose eq241 eq50472
    | (have j0 := eq50472 X1
       grind)
    | exact resolve eq50472 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50472
  have eq50486 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq50474 X0
       have i₂ := eq241 sF3 X1
       grind)
    | (have i₁ := eq50474 X0
       have i₂ := eq241 X0 sF3
       grind)
    | exact superpose eq241 eq50474
    | (have j0 := eq50474 X1
       grind)
    | exact resolve eq50474 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50474
  have eq51156 : ∀ X0 X2 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq50486 x X2
       have i₂ := eq10150 X0 x
       grind)
    | exact superpose eq10150 eq50486
    | (have j0 := eq50486 X0 X2
       grind)
    | exact resolve eq50486 eq10150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10150 eq50486
  have eq59238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq59246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq59238
    | exact resolve eq59238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59238
  have eq59251 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq59246
       have r₂ := eq27
       grind)
    | exact resolve eq59246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59246
  have eq59253 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq59251
    | exact resolve eq59251 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59251
  have eq59258 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq59253 eq10383
    | exact resolve eq10383 eq59253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59253
  have eq59385 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq59258
    | exact resolve eq59258 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59258
  have eq59386 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq59385
  have eq59390 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59386
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq59386
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq59386
    | exact resolve eq59386 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59441 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10688 y x
       have i₂ := eq59386
       grind)
    | exact superpose eq59386 eq10688
    | exact resolve eq10688 eq59386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59484 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq51156 y X0
       have i₂ := eq59386
       grind)
    | exact superpose eq59386 eq51156
    | (have j0 := eq51156 X0 X0
       grind)
    | exact resolve eq51156 eq59386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59386
  have eq59504 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq59484 X0
       grind)
    | (have r₁ := eq59484 X0
       have r₂ := eq24
       grind)
    | exact resolve eq59484 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59484
  have eq59523 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59441 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59441
    | (have j0 := eq59441 X0
       grind)
    | exact resolve eq59441 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59441
  have eq60087 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13659 X0 sF0
       have i₂ := eq59390 sF0
       grind)
    | exact superpose eq59390 eq13659
    | exact resolve eq13659 eq59390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13659 eq59390
  have eq60184 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60087 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60087
    | (have j0 := eq60087 X0
       grind)
    | exact resolve eq60087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60087
  have eq60308 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq60184
    | (have j0 := eq60184 X0
       grind)
    | exact resolve eq60184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60184
  have eq61216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq59504 sF4
       grind)
    | exact superpose eq59504 eq52
    | exact resolve eq52 eq59504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59504
  have eq61288 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq61216
    | exact resolve eq61216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61216
  have eq61723 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61288 eq27
    | exact resolve eq27 eq61288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61288
  have eq63069 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59523 sF3
       have i₂ := eq60308 sF3
       grind)
    | exact superpose eq60308 eq59523
    | exact resolve eq59523 eq60308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59523 eq60308
  have eq63128 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq63069
  have eq63156 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq63128
       have r₂ := eq61723
       grind)
    | exact resolve eq63128 eq61723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61723 eq63128
  have eq63251 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63156 eq77
    | (have r₁ := eq77
       have r₂ := eq63156
       grind)
    | exact resolve eq77 eq63156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq63156
  have eq63267 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq63251
  have eq77031 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63267 eq60
    | exact resolve eq60 eq63267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63267
  have eq77045 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq77031
    | exact resolve eq77031 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77031
  have eq79292 : (τ (σ y)) = (M.op y y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77045 eq10383
    | exact resolve eq10383 eq77045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77045
  have eq79427 : y = (M.op y y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq79292
    | exact resolve eq79292 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79292
  have eq79429 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq79427
       have r₂ := eq76
       grind)
    | exact resolve eq79427 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq79427
  have eq79431 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq44
    | exact resolve eq44 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq79440 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79429
  have eq79447 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq79440
  have eq79455 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79447
    | exact resolve eq79447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79447
  have eq79464 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79431
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79431
    | exact resolve eq79431 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79431
  have eq79472 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79455
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79455
    | exact resolve eq79455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79455
  have eq79524 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79472
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq79472
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq79472
    | exact resolve eq79472 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79472
  have eq80234 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq79524 sF0
       grind)
    | exact superpose eq79524 eq51
    | exact resolve eq51 eq79524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79524
  have eq80419 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80234
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80234
    | exact resolve eq80234 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80234
  have eq80420 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq80419
  have eq80540 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80420 eq20
    | exact resolve eq20 eq80420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80542 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq80420 eq51
    | exact resolve eq51 eq80420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq80644 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq80699 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80540
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80540
    | exact resolve eq80540 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80540
  have eq80729 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80699 eq26
    | exact resolve eq26 eq80699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80699
  have eq83326 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80542 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80542
    | (have j0 := eq80542 x
       grind)
    | exact resolve eq80542 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80542
  have eq83781 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq80420 eq83326
    | exact resolve eq83326 eq80420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80420 eq83326
  have eq83834 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq83781
       have r₂ := eq80644
       grind)
    | exact resolve eq83781 eq80644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80644 eq83781
  have eq83835 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83834
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83834
    | exact resolve eq83834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83834
  have eq83893 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10688 x x
       have i₂ := eq83835
       grind)
    | exact superpose eq83835 eq10688
    | exact resolve eq10688 eq83835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688 eq83835
  have eq83985 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq83893
    | (have j0 := eq83893 X0
       grind)
    | exact resolve eq83893 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83893
  have eq86506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq83985 eq80729
    | exact resolve eq80729 eq83985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80729 eq83985
  have eq86507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq86506
  have eq86526 : x = (M.op x y) := by
    first
    | (have r₁ := eq86507
       have r₂ := eq27
       grind)
    | exact resolve eq86507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86507
  have eq86555 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq86526 eq20
    | exact resolve eq20 eq86526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq86714 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq86555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86555
    | exact resolve eq86555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86555
  have eq86748 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq86714 eq26
    | exact resolve eq26 eq86714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq86753 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq86714 eq52
    | exact resolve eq52 eq86714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq86792 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86714 eq79464
    | exact resolve eq79464 eq86714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79464
  have eq87547 : ∀ X0 X1 X2 : G, (τ (M.op X2 X2)) = (M.op X1 (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14647 X1 X0 X2
       have i₂ := eq86753 X0
       grind)
    | exact superpose eq86753 eq14647
    | exact resolve eq14647 eq86753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14647
  have eq103858 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86792 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq86792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86792
  have eq103866 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86748 eq103858
    | exact resolve eq103858 eq86748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103858
  have eq103872 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86748 eq103866
    | exact resolve eq103866 eq86748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103866
  have eq103877 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq103872
       have r₂ := eq27
       grind)
    | exact resolve eq103872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103872
  have eq321037 : ∀ X0 X2 : G, (σ (M.op x y)) ≠ (τ (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op X2 X2) := by
    intro X0 X2
    first
    | exact superpose eq87547 eq50482
    | (have j0 := eq50482 X0 X2
       grind)
    | exact resolve eq50482 eq87547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50482 eq87547
  have eq1829058 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq103877 eq10383
    | exact resolve eq10383 eq103877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103877
  have eq1829523 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1829058
    | exact resolve eq1829058 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829058
  have eq1829524 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1829523
  have eq1829689 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq51156 y X0
       have i₂ := eq1829524
       grind)
    | exact superpose eq1829524 eq51156
    | (have j0 := eq51156 X0 X0
       grind)
    | exact resolve eq51156 eq1829524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51156 eq1829524
  have eq1830001 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1829689 X0
       grind)
    | (have r₁ := eq1829689 X0
       have r₂ := eq24
       grind)
    | exact resolve eq1829689 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829689
  have eq1834794 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86753 sF4
       have i₂ := eq1830001 sF4
       grind)
    | exact superpose eq1830001 eq86753
    | exact resolve eq86753 eq1830001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830001
  have eq1835266 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86748 eq1834794
    | exact resolve eq1834794 eq86748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834794
  have eq1835267 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1835266
  have eq1835928 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1835267 eq27
    | exact resolve eq27 eq1835267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1835950 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1835267 eq86753
    | exact resolve eq86753 eq1835267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86753
  have eq1946675 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq86748 eq1835950
    | exact resolve eq1835950 eq86748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835950
  have eq1948529 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1835267 eq1946675
    | exact resolve eq1946675 eq1835267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946675
  have eq1948827 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq86748 eq1948529
    | exact resolve eq1948529 eq86748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86748 eq1948529
  have eq1948964 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1835267 eq1948827
    | exact resolve eq1948827 eq1835267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835267 eq1948827
  have eq1949121 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1948964
       have i₂ := eq241 sF1 x
       grind)
    | (have i₁ := eq1948964
       have i₂ := eq241 X0 sF1
       grind)
    | exact superpose eq241 eq1948964
    | exact resolve eq1948964 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq1949222 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq1948964 eq14742
    | exact resolve eq14742 eq1948964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14742 eq1948964
  have eq1949589 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq29 eq1949222
    | exact resolve eq1949222 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949222
  have eq1950660 : ∀ X1 : G, (σ (M.op x y)) ≠ (τ (σ y)) ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq321037 x X1
       have i₂ := eq1949121 x
       grind)
    | exact superpose eq1949121 eq321037
    | (have j0 := eq321037 x X1
       grind)
    | exact resolve eq321037 eq1949121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321037
  have eq1951627 : (τ (σ y)) = (M.op y y) := by
    first
    | (have i₁ := eq10383
       have i₂ := eq1949121 sF3
       grind)
    | exact superpose eq1949121 eq10383
    | exact resolve eq10383 eq1949121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383
  have eq1951725 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq1951627
       have i₂ := eq1949121 y
       grind)
    | exact superpose eq1949121 eq1951627
    | exact resolve eq1951627 eq1949121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951627
  have eq1952540 : ∀ X1 : G, y ≠ (σ (M.op x y)) ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X1
    first
    | exact superpose eq29 eq1950660
    | (have j0 := eq1950660 X1
       grind)
    | exact resolve eq1950660 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950660
  have eq1953436 : y = (σ y) := by
    first
    | exact superpose eq29 eq1951725
    | exact resolve eq1951725 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1951725
  have eq1953899 : (σ (M.op x y)) = (σ y) ∨ y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1952540 x
       have i₂ := eq1949121 x
       grind)
    | exact superpose eq1949121 eq1952540
    | exact resolve eq1952540 eq1949121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949121 eq1952540
  have eq1954461 : y ≠ (σ (M.op x y)) := by
    first
    | (have r₁ := eq1953899
       have r₂ := eq1835928
       grind)
    | exact resolve eq1953899 eq1835928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835928 eq1953899
  have eq2029515 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1949589 x
       grind)
    | exact superpose eq1949589 eq18
    | (have j1 := eq1949589 x
       grind)
    | exact resolve eq18 eq1949589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1949589
  have eq2029546 : x = y := by
    first
    | exact superpose eq86526 eq2029515
    | exact resolve eq2029515 eq86526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86526 eq2029515
  have eq2030895 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2029546
       grind)
    | exact superpose eq2029546 eq24
    | exact resolve eq24 eq2029546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2029546
  have eq2031288 : y = (σ x) := by
    first
    | exact superpose eq1953436 eq2030895
    | exact resolve eq2030895 eq1953436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953436 eq2030895
  have eq2031463 : y = (σ x) := by
    first
    | (have i₁ := eq2031288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2031288
    | exact resolve eq2031288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2031288
  have eq2031630 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq86714 eq2031463
    | exact resolve eq2031463 eq86714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86714 eq2031463
  have eq2031748 : False := by grind
  exact eq2031748

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq249 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq409 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X1 X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq409 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq537 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq524 X0
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 x (M.op x y)
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 (M.op x y) x
       grind)
    | exact resolve eq524 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq554 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq410 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq567 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq554 X0
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq554 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq640 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq413 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq413 X0 X1 X2
       grind)
    | exact superpose eq413 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq413 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq413 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq656 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq640 x X1 X2
       grind)
    | (have r₁ := eq640 x X1 X2
       have r₂ := eq241 x X1
       grind)
    | (have r₁ := eq640 X1 x X2
       have r₂ := eq241 x X1
       grind)
    | exact resolve eq640 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq797 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X1 X2 X3 X0 (M.op x x)
       have i₂ := eq54 x X0 X2
       grind)
    | exact superpose eq54 eq50
    | exact resolve eq50 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq841 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq797 X0 X1 X2 X3
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq797
    | exact resolve eq797 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1115 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq66 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq53 x X1 x X0
       grind)
    | exact superpose eq53 eq66
    | (have j0 := eq66 X0 X1 x X4
       grind)
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq1142 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1115 X0 X1 X4
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1115
    | (have j0 := eq1115 X0 X1 X4
       grind)
    | (have r₁ := eq1115 X0 (M.op X0 X0) X4
       have r₂ := eq249 X0 X0
       grind)
    | exact resolve eq1115 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1316 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0
       have i₂ := eq55 X0 (σ X0)
       grind)
    | exact superpose eq55 eq95
    | exact resolve eq95 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1323 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq51
    | (have j1 := eq95 X0 X0
       grind)
    | exact resolve eq51 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1366 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1368 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1375 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1316 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1383 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1368 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1368 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1368 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1384 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1375 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1375
    | (have j0 := eq1375 X0 X1
       grind)
    | exact resolve eq1375 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1401 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1384 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1384
    | (have j0 := eq1384 X0 X1
       grind)
    | exact resolve eq1384 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1552 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq306 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq306
    | exact resolve eq306 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1628 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq537 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq537
    | exact resolve eq537 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1799 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq656 X1 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq656
    | exact resolve eq656 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq2049 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1628 eq34
    | exact resolve eq34 eq1628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq2395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq249 X4 X3
       have i₂ := eq841 X3 X0 X1 X2
       grind)
    | exact superpose eq841 eq249
    | exact resolve eq249 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq7356 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1401 X0 (τ X1)
       grind)
    | exact superpose eq1401 eq34
    | (have j1 := eq1401 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1401
  have eq7386 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7356 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7356
    | (have j0 := eq7356 X0 X1
       grind)
    | exact resolve eq7356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq7463 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7386 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7386
    | (have j0 := eq7386 X0 X1
       grind)
    | exact resolve eq7386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386
  have eq8269 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq2049 eq2049
    | exact resolve eq2049 eq2049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq10258 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq567 eq1383
    | (have j0 := eq1383 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1383 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq10280 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq10258 X0
       grind)
    | (have r₁ := eq10258 X0
       have r₂ := eq8269 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq10258 X0
       have r₂ := eq8269 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq10258 eq8269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8269 eq10258
  have eq10467 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10280 eq37
    | exact resolve eq37 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq10468 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10280 eq35
    | exact resolve eq35 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq10469 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10280 eq36
    | exact resolve eq36 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq10280
  have eq10497 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq567 eq10469
    | exact resolve eq10469 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10469
  have eq10498 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq567 eq10468
    | exact resolve eq10468 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10468
  have eq10499 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq567 eq10467
    | exact resolve eq10467 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq10467
  have eq10584 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10497
       grind)
    | exact superpose eq10497 eq16
    | exact resolve eq16 eq10497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10497
  have eq10629 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq10498
       grind)
    | exact superpose eq10498 eq16
    | exact resolve eq16 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10676 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq10499 eq16
    | exact resolve eq16 eq10499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10499
  have eq19272 : (σ (k x x)) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1366 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1366
    | (have j0 := eq1366 x
       grind)
    | exact resolve eq1366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq19273 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1366 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1366
    | (have j0 := eq1366 y
       grind)
    | exact resolve eq1366 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq19399 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq51 eq19273
    | exact resolve eq19273 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19273
  have eq19400 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq51 eq19272
    | exact resolve eq19272 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19272
  have eq19421 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19399
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq19399
    | exact resolve eq19399 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq19399
  have eq19422 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19400
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq19400
    | exact resolve eq19400 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19400
  have eq19430 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq1142 x (σ y) (σ y)
       grind)
    | (have r₁ := eq19421
       have r₂ := eq1142 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq19421
       have r₂ := eq1142 (σ y) (σ y) x
       grind)
    | exact resolve eq19421 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19421
  have eq19431 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1142 x (σ x) (σ x)
       grind)
    | (have r₁ := eq19422
       have r₂ := eq1142 (σ x) (k (σ x) (σ x)) x
       grind)
    | (have r₁ := eq19422
       have r₂ := eq1142 (σ x) (σ x) x
       grind)
    | exact resolve eq19422 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq19422
  have eq19448 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq19431 eq49
    | exact resolve eq49 eq19431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq19453 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq10629 eq19448
    | exact resolve eq19448 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10629 eq19448
  have eq55141 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7463 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7463
  have eq55398 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq19430 eq55141
    | (have j0 := eq55141 X0 (σ y)
       grind)
    | exact resolve eq55141 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430 eq55141
  have eq55410 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq55398 X0
       have i₂ := eq241 sF3 X1
       grind)
    | (have i₁ := eq55398 X0
       have i₂ := eq241 X0 sF3
       grind)
    | exact superpose eq241 eq55398
    | (have j0 := eq55398 X1
       grind)
    | exact resolve eq55398 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55398
  have eq66117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq66125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq66117
    | exact resolve eq66117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66117
  have eq66130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq66125
       have r₂ := eq27
       grind)
    | exact resolve eq66125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66125
  have eq66132 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq66130
    | exact resolve eq66130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66130
  have eq66137 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq66132 eq10584
    | exact resolve eq10584 eq66132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584 eq66132
  have eq66273 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq66137
    | exact resolve eq66137 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66137
  have eq66274 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq66273
  have eq66278 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66274
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq66274
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq66274
    | exact resolve eq66274 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq66274
  have eq66989 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq66278 sF0
       grind)
    | exact superpose eq66278 eq51
    | exact resolve eq51 eq66278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66278
  have eq67133 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66989
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66989
    | exact resolve eq66989 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66989
  have eq67134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq67133
  have eq67259 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq67134 eq52
    | exact resolve eq52 eq67134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq68216 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq67259
    | (have j0 := eq67259 (σ x)
       grind)
    | exact resolve eq67259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67259
  have eq68651 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67134 eq68216
    | exact resolve eq68216 eq67134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68216
  have eq68673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq68651
  have eq68674 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq68673
    | exact resolve eq68673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68673
  have eq68762 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq68674 eq55410
    | (have j0 := eq55410 X0 X0
       grind)
    | exact resolve eq55410 eq68674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55410 eq68674
  have eq68795 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq68762 X0
       grind)
    | (have r₁ := eq68762 X0
       have r₂ := eq67134
       grind)
    | exact resolve eq68762 eq67134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67134 eq68762
  have eq69818 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10676
       have i₂ := eq68795 sF1
       grind)
    | exact superpose eq68795 eq10676
    | exact resolve eq10676 eq68795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10676 eq68795
  have eq69864 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq69818
    | exact resolve eq69818 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69818
  have eq70762 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69864 eq51
    | exact resolve eq51 eq69864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq69864
  have eq70919 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70762
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70762
    | exact resolve eq70762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70762
  have eq70920 : y = (M.op x y) := by grind
  clear eq70919
  have eq70969 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq70920 eq20
    | exact resolve eq20 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq71108 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq70969
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70969
    | exact resolve eq70969 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969
  have eq71132 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq71108 eq26
    | exact resolve eq26 eq71108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq71241 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq19431 eq1552
    | exact resolve eq1552 eq19431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq19431
  have eq71242 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq71241 X0
       have i₂ := eq1799 X0 sF2
       grind)
    | exact superpose eq1799 eq71241
    | exact resolve eq71241 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71241
  have eq71243 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq70920 eq71242
    | exact resolve eq71242 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71242
  have eq71244 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq71243 X0
       have i₂ := eq19453
       grind)
    | exact superpose eq19453 eq71243
    | exact resolve eq71243 eq19453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19453 eq71243
  have eq71245 : ∀ X0 : G, (M.op x (M.op (τ X0) (M.op x y))) = (τ (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq71244 X0
       have i₂ := eq1799 (τ X0) x
       grind)
    | exact superpose eq1799 eq71244
    | exact resolve eq71244 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq71244
  have eq71246 : ∀ X0 : G, (τ (M.op x (M.op X0 y))) = (M.op x (M.op (τ X0) y)) := by
    intro X0
    first
    | exact superpose eq70920 eq71245
    | exact resolve eq71245 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71245
  have eq71297 : (τ (M.op x (M.op (σ x) y))) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq28 eq71246
    | exact resolve eq71246 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq71246
  have eq71342 : (M.op x (M.op x y)) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | (have i₁ := eq71297
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71297
    | exact resolve eq71297 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71297
  have eq71385 : (M.op x y) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | exact superpose eq70920 eq71342
    | exact resolve eq71342 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71342
  have eq71403 : (M.op x y) = (τ (M.op x (M.op (σ x) y))) := by
    first
    | (have i₁ := eq71385
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71385
    | exact resolve eq71385 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq71385
  have eq71410 : y = (τ (M.op x (M.op (σ x) y))) := by
    first
    | exact superpose eq70920 eq71403
    | exact resolve eq71403 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71403
  have eq71415 : (σ y) = (M.op x (M.op (σ x) y)) := by
    first
    | exact superpose eq71410 eq15
    | exact resolve eq15 eq71410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71410
  have eq71460 : (σ y) = (M.op x (M.op (σ x) y)) := by
    first
    | (have i₁ := eq71415
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq71415
    | exact resolve eq71415 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq71415
  have eq71469 : (σ (M.op x y)) = (M.op x (M.op (σ x) y)) := by
    first
    | exact superpose eq71108 eq71460
    | exact resolve eq71460 eq71108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71108 eq71460
  have eq71479 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq71469 eq841
    | exact resolve eq841 eq71469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq71512 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71132 eq71479
    | exact resolve eq71479 eq71132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71132 eq71479
  have eq71856 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq71512 (M.op x x)
       grind)
    | exact superpose eq71512 eq54
    | exact resolve eq54 eq71512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq75472 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2395 X0 X1 X2 X3 x
       have i₂ := eq71512 x
       grind)
    | exact superpose eq71512 eq2395
    | exact resolve eq2395 eq71512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395 eq71512
  have eq75473 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq71856 eq75472
    | exact resolve eq75472 eq71856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71856 eq75472
  have eq75474 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq75473 x X1 x
       have i₂ := eq211 x X1 x
       grind)
    | (have i₁ := eq75473 x X1 y
       have i₂ := eq211 x X1 x
       grind)
    | exact superpose eq211 eq75473
    | (have j0 := eq75473 x X1 y
       grind)
    | exact resolve eq75473 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq75473
  have eq75475 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | exact superpose eq70920 eq75474
    | exact resolve eq75474 eq70920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70920 eq75474
  have eq75503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71469
       have i₂ := eq75475 sF2
       grind)
    | exact superpose eq75475 eq71469
    | exact resolve eq71469 eq75475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71469 eq75475
  have eq75606 : False := by grind
  exact eq75606

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_y_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq179 x X0
       have i₂ := eq179 x X1
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq176
    | exact resolve eq176 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq208 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq175
    | exact resolve eq175 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq179 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X2
       have i₂ := eq179 X0 X2
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq216 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211 X0 X1 X2
       have i₂ := eq178 X0 X0 X1
       grind)
    | exact superpose eq178 eq211
    | exact resolve eq211 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq217 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq210 X0 X1 X2
       have i₂ := eq213 X0 X0
       grind)
    | exact superpose eq213 eq210
    | (have j0 := eq210 X0 X1 X2
       grind)
    | (have r₁ := eq210 X0 (M.op X0 X0) X2
       have r₂ := eq213 X0 X0
       grind)
    | exact resolve eq210 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq218 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq209 X0 X1 X2 X3
       have i₂ := eq213 X0 X0
       grind)
    | exact superpose eq213 eq209
    | exact resolve eq209 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq219 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq213 X0 X0
       grind)
    | exact superpose eq213 eq208
    | exact resolve eq208 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq220 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq213 X0 X0
       grind)
    | exact superpose eq213 eq207
    | exact resolve eq207 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq342 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq213 X3 X2
       have i₂ := eq216 X1 X2 X0
       grind)
    | (have i₁ := eq213 X0 (M.op X0 X0)
       have i₂ := eq216 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq216 eq213
    | exact resolve eq213 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq216
  have eq628 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq666 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq682 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (M.op X0 X0)
       have i₂ := eq666 (τ X1) X0
       grind)
    | exact superpose eq666 eq34
    | exact resolve eq34 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq744 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X1 (M.op X0 X0)
       have i₂ := eq666 (σ X1) X0
       grind)
    | exact superpose eq666 eq628
    | exact resolve eq628 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq666
  have eq1659 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1664 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq206 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq11
    | exact resolve eq11 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1785 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq4576 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq682 X1 (σ (M.op X1 X1))
       have i₂ := eq1785 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1785 eq682
    | (have j1 := eq1785 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq682 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq4578 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X1 (τ (M.op X1 X1))
       have i₂ := eq1785 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1785 eq744
    | (have j1 := eq1785 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq744 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4583 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq4584 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4585 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4576
  have eq4774 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (M.op X2 (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq178 X0 (M.op X0 X0) X2
       have i₂ := eq4584 (M.op X0 X0) x
       grind)
    | exact superpose eq4584 eq178
    | exact resolve eq178 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq4584
  have eq4892 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4585 X2 (M.op x x)
       have i₂ := eq342 (M.op x x) x X0 X1
       grind)
    | (have i₁ := eq4585 X2 (M.op x x)
       have i₂ := eq342 X0 X1 (M.op x x) x
       grind)
    | exact superpose eq342 eq4585
    | exact resolve eq4585 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq4911 : ∀ X0 X2 X3 X4 : G, (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (M.op X2 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq218 x X3 X2 X4
       have i₂ := eq4585 x X0
       grind)
    | exact superpose eq4585 eq218
    | exact resolve eq218 eq4585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4585
  have eq5028 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1659
       grind)
    | exact superpose eq1659 eq40
    | exact resolve eq40 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1659
  have eq5029 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5028
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5028
    | exact resolve eq5028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5028
  have eq5031 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq5029
    | exact resolve eq5029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5029
  have eq100120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5031 eq1664
    | exact resolve eq1664 eq5031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq5031
  have eq100131 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq100120
       have r₂ := eq27
       grind)
    | exact resolve eq100120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100120
  have eq100170 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq100131 eq744
    | exact resolve eq744 eq100131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq100131
  have eq100474 : ∀ X0 : G, y = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq100170
    | exact resolve eq100170 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100170
  have eq100591 : ∀ X0 : G, y = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100474 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq100474 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq100474 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100474
  have eq100671 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4583 X0 y
       have i₂ := eq100591 y
       grind)
    | exact superpose eq100591 eq4583
    | (have j0 := eq4583 X0 y
       grind)
    | (have r₁ := eq4583 X0 y
       have r₂ := eq100591 y
       grind)
    | exact resolve eq4583 eq100591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583 eq100591
  have eq100695 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100671
  have eq102473 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq175 sF0
       have i₂ := eq100695 sF0
       grind)
    | exact superpose eq100695 eq175
    | exact resolve eq175 eq100695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq100695
  have eq102589 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102473
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102473
    | exact resolve eq102473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102473
  have eq102590 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq102589
  have eq103086 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq102590 eq220
    | exact resolve eq220 eq102590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq104419 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq103086
    | (have j0 := eq103086 X0 (σ x)
       grind)
    | exact resolve eq103086 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103086
  have eq105125 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102590 eq104419
    | exact resolve eq104419 eq102590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104419
  have eq105220 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq105125
    | (have j0 := eq105125 X0
       grind)
    | exact resolve eq105125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105125
  have eq105252 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102590 eq105220
    | exact resolve eq105220 eq102590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102590 eq105220
  have eq105453 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq4774 x x
       have i₂ := eq105252 x
       grind)
    | exact superpose eq105252 eq4774
    | exact resolve eq4774 eq105252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774 eq105252
  have eq106268 : ∀ X1 : G, y = (M.op X1 y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq31 eq105453
    | exact resolve eq105453 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq105453
  have eq108994 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq106268 x
       grind)
    | exact superpose eq106268 eq18
    | (have j1 := eq106268 x
       grind)
    | exact resolve eq18 eq106268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106268
  have eq108995 : y = (M.op x y) := by grind
  clear eq108994
  have eq109004 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq108995
       grind)
    | exact superpose eq108995 eq18
    | exact resolve eq18 eq108995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq109005 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq108995
       grind)
    | exact superpose eq108995 eq24
    | exact resolve eq24 eq108995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq108995
  have eq109016 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq109005 eq20
    | exact resolve eq20 eq109005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109005
  have eq109091 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq109004 eq219
    | exact resolve eq219 eq109004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq109132 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109004 eq109091
    | exact resolve eq109091 eq109004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109004 eq109091
  have eq109278 : ∀ X1 X2 X3 : G, (M.op x y) = (M.op X1 (M.op X2 (M.op X1 X3))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq218 x X2 X1 X3
       have i₂ := eq109132 x
       grind)
    | exact superpose eq109132 eq218
    | exact resolve eq218 eq109132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq109348 : ∀ X1 X2 X3 : G, (σ (M.op x y)) = (M.op X1 (M.op X2 (M.op X1 X3))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4911 x X1 X2 X3
       have i₂ := eq109132 x
       grind)
    | exact superpose eq109132 eq4911
    | exact resolve eq4911 eq109132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4911
  have eq109609 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4892 (M.op x x) x X0
       have i₂ := eq109132 (M.op x x)
       grind)
    | exact superpose eq109132 eq4892
    | exact resolve eq4892 eq109132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892
  have eq109663 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq194 X0 (M.op sF2 (M.op X0 sF4))
       have i₂ := eq109132 (M.op sF2 (M.op X0 sF4))
       grind)
    | exact superpose eq109132 eq194
    | exact resolve eq194 eq109132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq109871 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq109609
    | (have j0 := eq109609 X0
       grind)
    | exact resolve eq109609 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109609
  have eq110088 : ∀ X1 X2 X3 : G, (σ (M.op x y)) = (M.op X1 (M.op X2 (M.op X1 X3))) := by
    intro X1 X2 X3
    first
    | exact superpose eq20 eq109348
    | (have j0 := eq109348 X1 X2 X3
       grind)
    | exact resolve eq109348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq109348
  have eq110244 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq109016 eq109871
    | exact resolve eq109871 eq109016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109016 eq109871
  have eq110425 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq110088 x x x
       have i₂ := eq109278 x x x
       grind)
    | exact superpose eq109278 eq110088
    | exact resolve eq110088 eq109278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109278 eq110088
  have eq110487 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq110244 x
       have i₂ := eq109132 x
       grind)
    | exact superpose eq109132 eq110244
    | exact resolve eq110244 eq109132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109132 eq110244
  have eq112689 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq110487 eq26
    | exact resolve eq26 eq110487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq110487
  have eq112733 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109663 eq112689
    | exact resolve eq112689 eq109663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109663 eq112689
  have eq112752 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq112733 eq27
    | exact resolve eq27 eq112733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq112733
  have eq112861 : False := by grind
  exact eq112861

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq108 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq108 x X0
       have i₂ := eq108 x X1
       grind)
    | exact superpose eq108 eq108
    | exact resolve eq108 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq129 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq120
    | exact resolve eq120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq120
  have eq2321 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq7374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq2321 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq2321 X0 X1
       grind)
    | exact superpose eq2321 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq2321 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq2321 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq2321 X0 X1
       grind)
    | exact resolve eq13 eq2321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq7381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7374
  have eq7382 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7381
  have eq7389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7382 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7382
    | (have j0 := eq7382 X0 X1
       grind)
    | exact resolve eq7382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7382
  have eq7390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq7389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7389
  have eq45876 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7390 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq7390
    | (have j0 := eq7390 (τ X0) (τ X1)
       grind)
    | exact resolve eq7390 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq45906 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45876 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45876
    | (have j0 := eq45876 X0 X1
       grind)
    | exact resolve eq45876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45876
  have eq45919 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45906 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45906
    | (have j0 := eq45906 X0 X1
       grind)
    | exact resolve eq45906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45906
  have eq45920 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45919 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45919
    | (have j0 := eq45919 X0 X1
       grind)
    | exact resolve eq45919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45919
  have eq45921 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45920 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45920
    | (have j0 := eq45920 X0 X1
       grind)
    | exact resolve eq45920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45920
  have eq45922 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45921 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45921
    | (have j0 := eq45921 X0 X1
       grind)
    | exact resolve eq45921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45921
  have eq45925 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7390 X0 X1
       have i₂ := eq45922 X0 X1
       grind)
    | exact superpose eq45922 eq7390
    | (have j0 := eq7390 X0 X1
       have j1 := eq45922 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq7390 eq45922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390 eq45922
  have eq2121901 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45925 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45925
  have eq2122707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2121901 x y
       grind)
    | exact superpose eq2121901 eq16
    | (have j1 := eq2121901 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2121901 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2121901 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq2121901 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq2121901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121901
  have eq2123073 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2122707
  have eq2123153 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2123073
       grind)
    | exact superpose eq2123073 eq10
    | exact resolve eq10 eq2123073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123073
  have eq2123339 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2123153
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2123153
    | exact resolve eq2123153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123153
  have eq2123340 : x = y := by grind
  clear eq2123339
  have eq2123341 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2123340
       grind)
    | exact superpose eq2123340 eq16
    | exact resolve eq16 eq2123340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123340
  have eq2123342 : False := by grind
  exact eq2123342

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation3292 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq55 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
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
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq79
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq102 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq98
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq102
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq36
  have eq244 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq233 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq233
    | exact resolve eq233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq245 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq244
  have eq502 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq59 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 (M.op X1 X0)
       have i₂ := eq59 X0 X1 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq746 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq134 eq245
    | exact resolve eq245 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq245
  have eq771 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | exact superpose eq218 eq746
    | exact resolve eq746 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq746
  have eq772 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq771
       have i₂ := eq216 (M.op y y)
       grind)
    | exact superpose eq216 eq771
    | exact resolve eq771 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq773 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq128 eq772
    | exact resolve eq772 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq874 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq773 eq56
    | exact resolve eq56 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq773
  have eq13058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq13059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq13058
    | exact resolve eq13058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13058
  have eq13070 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq13059
       have r₂ := eq29
       grind)
    | exact resolve eq13059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13059
  have eq13077 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq13070 eq72
    | exact resolve eq72 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13070
  have eq13136 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq13077
    | exact resolve eq13077 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13077
  have eq13137 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13136
  have eq13179 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq502 x x
       have i₂ := eq13137
       grind)
    | exact superpose eq13137 eq502
    | exact resolve eq502 eq13137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq13137
  have eq13188 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13179
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq13179
    | exact resolve eq13179 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq13179
  have eq13214 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13188 eq128
    | exact resolve eq128 eq13188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq13225 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13188 eq55
    | exact resolve eq55 eq13188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13188
  have eq13272 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13225
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq13225
    | exact resolve eq13225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13225
  have eq13280 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13214
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq13214
    | exact resolve eq13214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13214
  have eq13358 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq13272
       grind)
    | exact superpose eq13272 eq103
    | exact resolve eq103 eq13272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq13272
  have eq13420 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq13358
    | exact resolve eq13358 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358
  have eq13435 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13280 eq874
    | exact resolve eq874 eq13280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq13280
  have eq13481 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq13435
    | exact resolve eq13435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13435
  have eq13570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13481 eq13420
    | exact resolve eq13420 eq13481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13420 eq13481
  have eq13602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13570
  have eq13623 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13602
       have r₂ := eq29
       grind)
    | exact resolve eq13602 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13602
  have eq13631 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13623 eq31
    | exact resolve eq31 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13623
  have eq13738 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq13631
    | exact resolve eq13631 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13631
  have eq13739 : x = y := by grind
  clear eq13738
  have eq13756 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq13739
       grind)
    | exact superpose eq13739 eq20
    | exact resolve eq20 eq13739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13757 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq13739
       grind)
    | exact superpose eq13739 eq26
    | exact resolve eq26 eq13739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13739
  have eq13863 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13757
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13757
    | exact resolve eq13757 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13757
  have eq13878 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13863 eq28
    | exact resolve eq28 eq13863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13863
  have eq14111 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13878 eq72
    | exact resolve eq72 eq13878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq13878
  have eq14176 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14111
       have i₂ := eq13756
       grind)
    | exact superpose eq13756 eq14111
    | exact resolve eq14111 eq13756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756 eq14111
  have eq14207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14176 eq15
    | exact resolve eq15 eq14176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14176
  have eq14250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq14207
    | exact resolve eq14207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14207
  have eq14259 : False := by grind
  exact eq14259

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation3292 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq55 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X2 X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
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
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 (M.op X2 X3))))) := by
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
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq80
    | exact resolve eq80 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq86
    | exact resolve eq86 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq97 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq36
  have eq240 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq228
    | exact resolve eq228 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq241 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq240
  have eq482 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X2 X1)
       have i₂ := eq59 X1 X2 X0
       grind)
    | (have i₁ := eq14 X0 X0 X2
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq129 eq241
    | exact resolve eq241 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq241
  have eq752 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | exact superpose eq213 eq727
    | exact resolve eq727 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq753 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq752
       have i₂ := eq211 (M.op y y)
       grind)
    | exact superpose eq211 eq752
    | exact resolve eq752 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq754 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq123 eq753
    | exact resolve eq753 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq753
  have eq770 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 X1 (σ X0) (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq60
    | exact resolve eq60 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq850 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq754 eq56
    | exact resolve eq56 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1133 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) = (M.op X1 (M.op X4 (M.op X2 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq58 X2 x X1 X4
       have i₂ := eq59 (M.op X1 X2) x X0
       grind)
    | (have i₁ := eq58 X0 (M.op X2 X0) X2 x
       have i₂ := eq59 (M.op X2 X0) X1 (M.op (M.op X2 X0) (M.op X2 X0))
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq59
  have eq11060 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1133 X0 X1 X2 x
       have i₂ := eq482 x X2 X1
       grind)
    | exact superpose eq482 eq1133
    | exact resolve eq1133 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq1133
  have eq12036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq12037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq12036
    | exact resolve eq12036 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12048 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq12037
       have r₂ := eq29
       grind)
    | exact resolve eq12037 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq12207 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12048 eq72
    | exact resolve eq72 eq12048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12048
  have eq12257 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq12207
    | exact resolve eq12207 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12207
  have eq12258 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12257
  have eq12300 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11060 X0 x x
       have i₂ := eq12258
       grind)
    | exact superpose eq12258 eq11060
    | exact resolve eq11060 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11060
  have eq12302 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12300 x
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq12300
    | exact resolve eq12300 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq12300
  have eq12363 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12302 eq55
    | exact resolve eq55 eq12302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12302
  have eq12407 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12363
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12363
    | exact resolve eq12363 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12640 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op X1 (M.op X0 (σ y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq770 x X1 x
       have i₂ := eq12258
       grind)
    | exact superpose eq12258 eq770
    | exact resolve eq770 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq12258
  have eq12795 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12640 x x
       have i₂ := eq14 (σ y) x x
       grind)
    | exact superpose eq14 eq12640
    | exact resolve eq12640 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12640
  have eq12838 : (σ y) = (M.op (σ x) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12795
       have i₂ := eq46 y
       grind)
    | exact superpose eq46 eq12795
    | exact resolve eq12795 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq12795
  have eq12867 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12838
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq12838
    | exact resolve eq12838 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12838
  have eq12887 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq213 eq12867
    | exact resolve eq12867 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq12867
  have eq12900 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq754 eq12887
    | exact resolve eq12887 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq12887
  have eq12909 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12900
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq12900
    | exact resolve eq12900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12900
  have eq12918 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12909 eq850
    | exact resolve eq850 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq12909
  have eq12962 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq12918
    | exact resolve eq12918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12918
  have eq12978 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq12407
       grind)
    | exact superpose eq12407 eq98
    | exact resolve eq98 eq12407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq12407
  have eq13038 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq12978
    | exact resolve eq12978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12978
  have eq13295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13038 eq12962
    | exact resolve eq12962 eq13038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962 eq13038
  have eq13324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13295
  have eq13338 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13324
       have r₂ := eq29
       grind)
    | exact resolve eq13324 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq13354 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13338 eq31
    | exact resolve eq31 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13338
  have eq13461 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq13354
    | exact resolve eq13354 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13354
  have eq13462 : x = y := by grind
  clear eq13461
  have eq13479 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq13462
       grind)
    | exact superpose eq13462 eq20
    | exact resolve eq20 eq13462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13480 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq13462
       grind)
    | exact superpose eq13462 eq26
    | exact resolve eq26 eq13462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13462
  have eq13586 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13480
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13480
    | exact resolve eq13480 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13480
  have eq13601 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13586 eq28
    | exact resolve eq28 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13586
  have eq13846 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13601 eq72
    | exact resolve eq72 eq13601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq13601
  have eq13909 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13846
       have i₂ := eq13479
       grind)
    | exact superpose eq13479 eq13846
    | exact resolve eq13846 eq13479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13479 eq13846
  have eq13943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13909 eq15
    | exact resolve eq15 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq13986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq13943
    | exact resolve eq13943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13943
  have eq13995 : False := by grind
  exact eq13995
