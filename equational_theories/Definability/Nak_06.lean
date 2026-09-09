import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq444 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3042 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq444 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq444 X0 X1
       grind)
    | exact superpose eq444 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq444 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq444 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq444 X0 X1
       grind)
    | exact resolve eq13 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq3044 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3042 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3045 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3044 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3937 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3045 X0 X1
       grind)
    | exact superpose eq3045 eq28
    | (have j1 := eq3045 X0 X1
       grind)
    | exact resolve eq28 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3045
  have eq3972 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3937 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq3987 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3972 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3972
    | exact resolve eq3972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq4088 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3987 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq3987
    | (have j0 := eq3987 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq3987 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3987
  have eq4140 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4088 X1 X0
       grind)
    | exact superpose eq4088 eq11
    | (have j1 := eq4088 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq4259 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4140 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4140
    | (have j0 := eq4140 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq4140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140
  have eq4289 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4259 X0 (τ X1)
       grind)
    | exact superpose eq4259 eq19
    | (have j1 := eq4259 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4259 (σ X0) (σ X1)
       grind)
    | exact superpose eq4259 eq15
    | (have j1 := eq4259 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq4553 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4289 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4289
    | exact resolve eq4289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq4615 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4553 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4553
    | (have j0 := eq4553 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq4553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4553
  have eq4993 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4311 x y
       grind)
    | exact superpose eq4311 eq16
    | (have j1 := eq4311 x y
       grind)
    | exact resolve eq16 eq4311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq5035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4993
       have i₂ := eq4615 y x
       grind)
    | exact superpose eq4615 eq4993
    | (have j1 := eq4615 (σ x) (σ y)
       grind)
    | (have r₁ := eq4993
       have r₂ := eq4615 y x
       grind)
    | (have r₁ := eq4993
       have r₂ := eq4615 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4993
       have r₂ := eq4615 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4993 eq4615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4615 eq4993
  have eq5038 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5035
  have eq5041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5038
       grind)
    | exact superpose eq5038 eq16
    | exact resolve eq16 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq5042 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5041
       have r₂ := eq22 x
       grind)
    | exact resolve eq5041 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041
  have eq5043 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5042
       grind)
    | exact superpose eq5042 eq16
    | exact resolve eq16 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5044 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5042
       grind)
    | exact superpose eq5042 eq10
    | exact resolve eq10 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq5097 : x = y := by
    first
    | (have i₁ := eq5044
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5044
    | exact resolve eq5044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044
  have eq5098 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5043
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5043
    | exact resolve eq5043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5043
  have eq5099 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5098
       have i₂ := eq5097
       grind)
    | exact superpose eq5097 eq5098
    | exact resolve eq5098 eq5097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5097 eq5098
  have eq5100 : False := by grind
  exact eq5100

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pyy_pxx_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq63 (M.op X0 X1)
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | (have r₁ := eq91 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq91 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq450 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 X0 (M.op X0 X1)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq454 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq450
    | (have j0 := eq450 X0 X1
       grind)
    | exact resolve eq450 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq455 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq622 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq455
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq637 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq622 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq638 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq639 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq641 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq639 (σ y) (σ x)
       grind)
    | exact superpose eq639 eq16
    | (have j1 := eq639 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq639 X1 X0
       grind)
    | exact superpose eq639 eq102
    | (have j0 := eq102 X0 X1
       have j1 := eq639 X1 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq639 X0 X1
       grind)
    | exact resolve eq102 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq664 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq648 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq669 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq641
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq641
    | exact resolve eq641 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq672 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq664 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq664
    | exact resolve eq664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq664 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq664
    | exact resolve eq664 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq664
  have eq927 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq669
       have i₂ := eq639 y x
       grind)
    | exact superpose eq639 eq669
    | (have j1 := eq639 y x
       grind)
    | exact resolve eq669 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq669
  have eq933 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq927
  have eq950 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq672 x y
       grind)
    | exact superpose eq672 eq16
    | (have j1 := eq672 x y
       grind)
    | exact resolve eq16 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq1129 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq675 X1 X0
       grind)
    | exact superpose eq675 eq11
    | (have j1 := eq675 X1 X0
       grind)
    | exact resolve eq11 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq1130 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1129 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1129
    | (have j0 := eq1129 X0 X1
       grind)
    | exact resolve eq1129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1184 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1130
    | (have j0 := eq1130 X1 (σ X0)
       grind)
    | exact resolve eq1130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1249 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1184
    | (have j0 := eq1184 X0 X1
       grind)
    | exact resolve eq1184 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1184
  have eq1270 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1249 X0 X1
       grind)
    | exact superpose eq1249 eq18
    | (have j1 := eq1249 X0 X1
       grind)
    | exact resolve eq18 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1249
  have eq1471 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1270 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1270
    | (have j0 := eq1270 X1 (σ X0)
       grind)
    | exact resolve eq1270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1528 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1471 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1471
    | (have j0 := eq1471 X0 X1
       grind)
    | exact resolve eq1471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1532 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1528 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1528
    | (have j0 := eq1528 X0 X1
       grind)
    | exact resolve eq1528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq950
       have i₂ := eq1532 y x
       grind)
    | exact superpose eq1532 eq950
    | (have j1 := eq1532 y x
       grind)
    | (have r₁ := eq950
       have r₂ := eq1532 y x
       grind)
    | exact resolve eq950 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1569 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1532 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1570 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1545
  have eq1588 : (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq1569 x y
       grind)
    | (have r₁ := eq1570
       have r₂ := eq1569 x y
       grind)
    | exact resolve eq1570 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq1570
  have eq1602 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1588
       grind)
    | exact superpose eq1588 eq10
    | exact resolve eq10 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : y = (k x y) := by
    first
    | (have i₁ := eq1602
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1602
    | exact resolve eq1602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq2122 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq933
       have i₂ := eq1641
       grind)
    | exact superpose eq1641 eq933
    | exact resolve eq933 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq2154 : y ≠ y ∨ y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2122
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2122
       grind)
    | exact resolve eq13 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2176 : y = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2154
  have eq2179 : x = y ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2176
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq2176
    | exact resolve eq2176 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2186 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2179
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq2179
    | exact resolve eq2179 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq2189 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2186
       have i₂ := eq1641
       grind)
    | exact superpose eq1641 eq2186
    | exact resolve eq2186 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641 eq2186
  have eq2190 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2189
  have eq2191 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2190
       grind)
    | exact superpose eq2190 eq16
    | exact resolve eq16 eq2190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2207 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2191
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq2191
    | exact resolve eq2191 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2209 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2207
       have r₂ := eq63 (σ x)
       grind)
    | exact resolve eq2207 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2221 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2209
       grind)
    | exact superpose eq2209 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2209
       grind)
    | exact resolve eq13 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2243 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
  clear eq2221
  have eq2260 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2243
       have i₂ := eq63 (σ x)
       grind)
    | exact superpose eq63 eq2243
    | exact resolve eq2243 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2270 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2260
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2260
    | exact resolve eq2260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2276 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2270
       have i₂ := eq1588
       grind)
    | exact superpose eq1588 eq2270
    | exact resolve eq2270 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588 eq2270
  have eq2279 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2276
       have i₂ := eq63 (σ x)
       grind)
    | exact superpose eq63 eq2276
    | exact resolve eq2276 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2280 : (σ x) = (σ y) := by grind
  clear eq2279
  have eq2283 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2280
       grind)
    | exact superpose eq2280 eq16
    | exact resolve eq16 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2284 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2280
       grind)
    | exact superpose eq2280 eq10
    | exact resolve eq10 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2324 : x = y := by
    first
    | (have i₁ := eq2284
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2284
    | exact resolve eq2284 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2325 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq2283
       have i₂ := eq63 (σ x)
       grind)
    | exact superpose eq63 eq2283
    | exact resolve eq2283 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2326 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2325
       have i₂ := eq2324
       grind)
    | exact superpose eq2324 eq2325
    | exact resolve eq2325 eq2324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2324 eq2325
  have eq2327 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2326
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq2326
    | exact resolve eq2326 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2326
  have eq2328 : False := by grind
  exact eq2328

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pyy_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq40
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq91 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq99 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq107 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq112 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq107
    | (have j0 := eq107 X0 X1
       grind)
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq115 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq99
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq99 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq140 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq143 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq624 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq624
    | (have j0 := eq624 X0 X1
       grind)
    | exact resolve eq624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq4084 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140 x (σ y)
       grind)
    | exact superpose eq140 eq16
    | (have j1 := eq140 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq140 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4086 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq140 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq140 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq140 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq4105 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4086 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq4112 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4105 X0 X1
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq4105
    | (have j0 := eq4105 X0 X1
       grind)
    | exact resolve eq4105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4113 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4114 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4084
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4084
    | exact resolve eq4084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084
  have eq4564 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4113 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4113
    | exact resolve eq4113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4611 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X1) X0
       have i₂ := eq4113 X1 (σ X0)
       grind)
    | exact superpose eq4113 eq91
    | (have j1 := eq4113 X0 (σ X1)
       grind)
    | exact resolve eq91 eq4113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq4113
  have eq4673 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4611 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4611
    | (have j0 := eq4611 X0 X1
       grind)
    | exact resolve eq4611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq4682 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4564 X0 X1
       have i₂ := eq115 X1 X0
       grind)
    | exact superpose eq115 eq4564
    | (have j0 := eq4564 X0 X1
       grind)
    | exact resolve eq4564 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq4564
  have eq4705 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4673 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4673
    | (have j0 := eq4673 X0 X1
       grind)
    | exact resolve eq4673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq4712 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4705 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4705
    | (have j0 := eq4705 X0 X1
       grind)
    | exact resolve eq4705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705
  have eq4784 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4682 X0 X1
       grind)
    | exact superpose eq4682 eq11
    | (have j1 := eq4682 X0 X1
       grind)
    | exact resolve eq11 eq4682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq4892 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4784 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4784
    | (have j0 := eq4784 X0 X1
       grind)
    | exact resolve eq4784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4962 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4892 (τ X0) X1
       grind)
    | exact superpose eq4892 eq18
    | (have j1 := eq4892 (τ X0) X1
       grind)
    | exact resolve eq18 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4892
  have eq5866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4712 X1 X0
       grind)
    | exact superpose eq4712 eq11
    | (have j1 := eq4712 X1 X0
       grind)
    | exact resolve eq11 eq4712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq6779 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5866 x y
       grind)
    | exact superpose eq5866 eq16
    | (have j1 := eq5866 x y
       grind)
    | exact resolve eq16 eq5866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5866
  have eq6889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6779
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq6779
    | (have j1 := eq502 y (M.op x y)
       grind)
    | (have r₁ := eq6779
       have r₂ := eq502 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6779
       have r₂ := eq502 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6779 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq6779
  have eq6894 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6889
  have eq6922 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6894
       grind)
    | exact superpose eq6894 eq16
    | exact resolve eq16 eq6894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6894
  have eq6923 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6922
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq6922
    | exact resolve eq6922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq6924 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6923
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6923
    | exact resolve eq6923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq6925 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6924
  have eq7158 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq6925
       grind)
    | exact superpose eq6925 eq25
    | exact resolve eq25 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7168 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7331 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7158
       have i₂ := eq6925
       grind)
    | exact superpose eq6925 eq7158
    | exact resolve eq7158 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925 eq7158
  have eq7350 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7331
  have eq7353 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7350
       have r₂ := eq7168
       grind)
    | exact resolve eq7350 eq7168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168 eq7350
  have eq8360 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4962 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4962
    | exact resolve eq4962 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq8482 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8360 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8360
    | (have j0 := eq8360 X0 X1
       grind)
    | exact resolve eq8360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq38009 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4114
       have i₂ := eq7353
       grind)
    | exact superpose eq7353 eq4114
    | exact resolve eq4114 eq7353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114 eq7353
  have eq38015 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38009
  have eq38016 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38015
  have eq38024 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38016
       grind)
    | exact superpose eq38016 eq10
    | exact resolve eq10 eq38016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38016
  have eq38130 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38024
    | exact resolve eq38024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38024
  have eq38411 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38130
       grind)
    | exact superpose eq38130 eq16
    | exact resolve eq16 eq38130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38130
  have eq38412 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38411
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38411
    | exact resolve eq38411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38411
  have eq38413 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38412
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38412
    | exact resolve eq38412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38412
  have eq38414 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38413
  have eq38441 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38414
       grind)
    | exact superpose eq38414 eq11
    | exact resolve eq11 eq38414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38414
  have eq38863 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq16
    | exact resolve eq16 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38892 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq25
    | exact resolve eq25 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq38863
       have i₂ := eq8482 x y
       grind)
    | exact superpose eq8482 eq38863
    | (have j1 := eq8482 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38863
       have r₂ := eq8482 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38863 eq8482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482
  have eq39004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq659 y x
       grind)
    | exact superpose eq659 eq38863
    | (have j1 := eq659 x y
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 y x
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38863
       have r₂ := eq659 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38863 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq39005 : x = y ∨ x = (M.op x y) := by grind
  clear eq39004
  have eq39006 : x = y ∨ y = (k x y) := by grind
  clear eq39003
  have eq39271 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39005
       grind)
    | exact superpose eq39005 eq38863
    | exact resolve eq38863 eq39005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39005
  have eq39272 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39271
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39271
    | exact resolve eq39271 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39271
  have eq39276 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39272
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39272
    | exact resolve eq39272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39272
  have eq39277 : x = (M.op x y) := by grind
  clear eq39276
  have eq39664 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39006
       grind)
    | exact superpose eq39006 eq38863
    | exact resolve eq38863 eq39006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39006
  have eq39668 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39664
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39664
    | exact resolve eq39664 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq39664
  have eq39672 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39668
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39668
    | exact resolve eq39668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39668
  have eq39673 : y = (k x y) := by grind
  clear eq39672
  have eq40142 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq38863
    | exact resolve eq38863 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38863
  have eq40182 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40142
       have i₂ := eq39277
       grind)
    | exact superpose eq39277 eq40142
    | exact resolve eq40142 eq39277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39277 eq40142
  have eq40980 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq38892
       have i₂ := eq113 x (k x y)
       grind)
    | exact superpose eq113 eq38892
    | (have j1 := eq113 x (k x y)
       grind)
    | exact resolve eq38892 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq38892
  have eq41043 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq40980
    | exact resolve eq40980 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40980
  have eq41044 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41043
  have eq41060 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41044
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq41044
    | exact resolve eq41044 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41044
  have eq41072 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41060
       have i₂ := eq38441
       grind)
    | exact superpose eq38441 eq41060
    | exact resolve eq41060 eq38441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38441 eq41060
  have eq41073 : (σ x) = (σ (k x y)) := by grind
  clear eq41072
  have eq41080 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41073
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq41073
    | exact resolve eq41073 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39673 eq41073
  have eq41086 : False := by grind
  exact eq41086

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq518 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq545 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X0 X1
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq518
    | (have j0 := eq518 X0 X1
       grind)
    | exact resolve eq518 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq548 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq515
    | (have j0 := eq515 X0 X1
       grind)
    | exact resolve eq515 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq515
  have eq853 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq548
    | exact resolve eq548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq853
    | (have j0 := eq853 X0 X1
       grind)
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq879 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq545
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq545
    | exact resolve eq545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq885
  have eq912 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq879
    | (have j0 := eq879 X0 X1
       grind)
    | exact resolve eq879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq947 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq877 X1 X0
       grind)
    | exact superpose eq877 eq10
    | (have j1 := eq877 X1 X0
       grind)
    | exact resolve eq10 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq947
    | (have j0 := eq947 X0 X1
       grind)
    | exact resolve eq947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1044 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq912 (σ x) y
       grind)
    | exact superpose eq912 eq16
    | (have j1 := eq912 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq912 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1049 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1044
    | exact resolve eq1044 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1254 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 (σ X0) X1
       have i₂ := eq908 X1 X0
       grind)
    | exact superpose eq908 eq160
    | (have j0 := eq160 (σ X0) X1
       have j1 := eq908 X1 X0
       grind)
    | (have r₁ := eq160 (σ X1) X0
       have r₂ := eq908 X0 X1
       grind)
    | (have r₁ := eq160 (σ X1) X1
       have r₂ := eq908 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq160 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq908
  have eq1262 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1263 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1262 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1272 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1263 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1263
    | exact resolve eq1263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq1263 X0 X1
       grind)
    | exact superpose eq1263 eq37
    | (have j1 := eq1263 X0 X1
       grind)
    | exact resolve eq37 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1263
  have eq1381 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1272 (τ X0) X1
       grind)
    | exact superpose eq1272 eq18
    | (have j1 := eq1272 (τ X0) X1
       grind)
    | exact resolve eq18 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1272
  have eq5490 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq1285 X1 (σ X0)
       grind)
    | exact superpose eq1285 eq28
    | (have j1 := eq1285 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1285
  have eq5549 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5490 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5490
    | (have j0 := eq5490 X0 X1
       grind)
    | exact resolve eq5490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490
  have eq5587 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5549 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5549
    | (have j0 := eq5549 X0 X1
       grind)
    | exact resolve eq5549 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549
  have eq5600 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5587 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5587
    | (have j0 := eq5587 X0 X1
       grind)
    | exact resolve eq5587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5686 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1381 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1381
    | exact resolve eq1381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq5755 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5686 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5686
    | (have j0 := eq5686 X0 X1
       grind)
    | exact resolve eq5686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686
  have eq5927 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq5600 X1 X0
       grind)
    | exact superpose eq5600 eq11
    | (have j1 := eq5600 X1 X0
       grind)
    | exact resolve eq11 eq5600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5600
  have eq6715 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5927 x y
       grind)
    | exact superpose eq5927 eq16
    | (have j1 := eq5927 x y
       grind)
    | exact resolve eq16 eq5927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5927
  have eq6799 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6715
       have i₂ := eq985 x y
       grind)
    | exact superpose eq985 eq6715
    | (have j1 := eq985 x y
       grind)
    | (have r₁ := eq6715
       have r₂ := eq985 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6715
       have r₂ := eq985 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6715 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985 eq6715
  have eq6807 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6799
  have eq6825 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6807
       grind)
    | exact superpose eq6807 eq16
    | exact resolve eq16 eq6807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6807
  have eq6826 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6825
       have r₂ := eq22 x
       grind)
    | exact resolve eq6825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6830 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq6826
       grind)
    | exact superpose eq6826 eq120
    | exact resolve eq120 eq6826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6841 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq6855 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6830
       have i₂ := eq6826
       grind)
    | exact superpose eq6826 eq6830
    | exact resolve eq6830 eq6826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6826 eq6830
  have eq6870 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6855
  have eq6873 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6870
       have r₂ := eq6841
       grind)
    | exact resolve eq6870 eq6841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841 eq6870
  have eq19063 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq6873
       grind)
    | exact superpose eq6873 eq1049
    | exact resolve eq1049 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq6873
  have eq19083 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq19063
  have eq19084 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq19083
  have eq19092 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19084
       grind)
    | exact superpose eq19084 eq10
    | exact resolve eq10 eq19084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19084
  have eq19160 : x = y ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq19092
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19092
    | exact resolve eq19092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092
  have eq19167 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19160
       grind)
    | exact superpose eq19160 eq16
    | exact resolve eq16 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19160
  have eq19170 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq19167
       have r₂ := eq22 x
       grind)
    | exact resolve eq19167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19167
  have eq19189 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19170
       grind)
    | exact superpose eq19170 eq16
    | exact resolve eq16 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19201 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq120 (σ x) (σ y)
       have i₂ := eq19170
       grind)
    | exact superpose eq19170 eq120
    | exact resolve eq120 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq19300 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19189
       have i₂ := eq5755 x y
       grind)
    | exact superpose eq5755 eq19189
    | (have j1 := eq5755 x y
       grind)
    | (have r₁ := eq19189
       have r₂ := eq5755 x y
       grind)
    | (have r₁ := eq19189
       have r₂ := eq5755 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19189
       have r₂ := eq5755 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19189 eq5755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq19301 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19189
       have i₂ := eq877 y x
       grind)
    | exact superpose eq877 eq19189
    | (have j1 := eq877 y x
       grind)
    | (have r₁ := eq19189
       have r₂ := eq877 y x
       grind)
    | (have r₁ := eq19189
       have r₂ := eq877 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19189
       have r₂ := eq877 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19189 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq19302 : x = y ∨ x = (M.op x y) := by grind
  clear eq19301
  have eq19303 : x = y ∨ y = (k x y) := by grind
  clear eq19300
  have eq19311 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19189
       have i₂ := eq19302
       grind)
    | exact superpose eq19302 eq19189
    | exact resolve eq19189 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19302
  have eq19312 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq19311
  have eq19313 : x = (M.op x y) := by grind
  clear eq19312
  have eq19404 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq19189
       have i₂ := eq19303
       grind)
    | exact superpose eq19303 eq19189
    | exact resolve eq19189 eq19303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19303
  have eq19408 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (k x y) := by grind
  clear eq19404
  have eq19409 : y = (k x y) := by grind
  clear eq19408
  have eq19423 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq19189
       have i₂ := eq19409
       grind)
    | exact superpose eq19409 eq19189
    | exact resolve eq19189 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19189
  have eq19445 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq19423
       have i₂ := eq19313
       grind)
    | exact superpose eq19313 eq19423
    | exact resolve eq19423 eq19313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19313 eq19423
  have eq19595 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19201
       have i₂ := eq545 x (k x y)
       grind)
    | exact superpose eq545 eq19201
    | (have j1 := eq545 x (k x y)
       grind)
    | exact resolve eq19201 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq19201
  have eq19643 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19595
       have i₂ := eq19409
       grind)
    | exact superpose eq19409 eq19595
    | exact resolve eq19595 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19595
  have eq19644 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq19643
  have eq19654 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19644
       have i₂ := eq19409
       grind)
    | exact superpose eq19409 eq19644
    | exact resolve eq19644 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19644
  have eq19663 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq19654
       have i₂ := eq19170
       grind)
    | exact superpose eq19170 eq19654
    | exact resolve eq19654 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19170 eq19654
  have eq19664 : (σ x) = (σ (k x y)) := by grind
  clear eq19663
  have eq19671 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19664
       have i₂ := eq19409
       grind)
    | exact superpose eq19409 eq19664
    | exact resolve eq19664 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409 eq19664
  have eq19676 : False := by grind
  exact eq19676

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq435 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq440 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq461 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq451 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq451 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq451 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq451 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq466 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq435
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq435 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq472 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq466
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq466
    | exact resolve eq466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq495 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq461 X1 (τ X0)
       grind)
    | exact superpose eq461 eq17
    | (have j1 := eq461 X1 (τ X0)
       grind)
    | exact resolve eq17 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq501 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq461 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq495 X1 (τ X0)
       grind)
    | exact superpose eq495 eq18
    | (have j1 := eq495 X1 (τ X0)
       grind)
    | exact resolve eq18 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq495
  have eq564 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq578 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq581 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq636 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq461 X0 X1
       grind)
    | exact superpose eq461 eq581
    | (have j0 := eq581 X1 X0
       have j1 := eq461 X1 X0
       grind)
    | exact resolve eq581 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq581
  have eq693 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq636 X0 X1
       have j1 := eq501 X0 X1
       grind)
    | (have r₁ := eq636 X0 X1
       have r₂ := eq501 X0 X1
       grind)
    | exact resolve eq636 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq636
  have eq718 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq472
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq472
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq472 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq718
  have eq720 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq719
       have r₂ := eq12 x y
       grind)
    | exact resolve eq719 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq734 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq693 X1 (σ X0)
       grind)
    | exact superpose eq693 eq22
    | (have j1 := eq693 X1 (σ X0)
       grind)
    | exact resolve eq22 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq693
  have eq767 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq786 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq767
    | (have j0 := eq767 X0 X1
       grind)
    | exact resolve eq767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1093 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq786
    | exact resolve eq786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq1154 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1093 x y
       grind)
    | exact superpose eq1093 eq16
    | (have j1 := eq1093 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1093 x y
       grind)
    | exact resolve eq16 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1170 : y = (k x y) := by grind
  clear eq1154
  have eq1391 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq720
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq720
    | exact resolve eq720 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1401 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq472
       have i₂ := eq1391
       grind)
    | exact superpose eq1391 eq472
    | exact resolve eq472 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq1391
  have eq1411 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1401
  have eq1412 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1411
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq1411
    | exact resolve eq1411 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1413 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1412
  have eq1416 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq16
    | exact resolve eq16 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1445 : (σ y) ≠ (σ y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1416
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1416
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1416 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1445
  have eq1448 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1446
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1446 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1449 : y = (M.op x y) := by
    first
    | (have i₁ := eq1448
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq1448
    | exact resolve eq1448 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq1448
  have eq1450 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1416
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq1416
    | exact resolve eq1416 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq1449
  have eq1462 : False := by grind
  exact eq1462

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq265 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq265 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq277 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq266 (σ X0)
       grind)
    | exact superpose eq266 eq15
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq266 (τ X0)
       grind)
    | exact superpose eq266 eq31
    | exact resolve eq31 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq283
    | exact resolve eq283 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq277
    | exact resolve eq277 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq277
  have eq409 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq418 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq417 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq437 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq418 X0 (τ X1)
       grind)
    | exact superpose eq418 eq18
    | (have j1 := eq418 X0 (τ X1)
       grind)
    | exact resolve eq18 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq418 (σ X0) (σ X1)
       grind)
    | exact superpose eq418 eq15
    | (have j1 := eq418 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq463 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq468 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq437
    | exact resolve eq437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq502 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq468
    | (have j0 := eq468 X0 X1
       grind)
    | exact resolve eq468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq846 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq463 x y
       grind)
    | exact superpose eq463 eq16
    | (have j1 := eq463 x y
       grind)
    | exact resolve eq16 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq876 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq846
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq846
    | (have j1 := eq502 y x
       grind)
    | (have r₁ := eq846
       have r₂ := eq502 y x
       grind)
    | exact resolve eq846 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq846
  have eq877 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq876
  have eq882 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq877
       grind)
    | exact resolve eq13 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq882
  have eq895 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq862 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq862
    | (have j0 := eq862 (τ X0) (τ X1)
       grind)
    | exact resolve eq862 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq911 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq895 X0 X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq895
    | (have j0 := eq895 X0 X1
       grind)
    | exact resolve eq895 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq919 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq911 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq911
    | (have j0 := eq911 X0 X1
       grind)
    | exact resolve eq911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq927 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq919
    | (have j0 := eq919 X0 X1
       grind)
    | exact resolve eq919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq931 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq934 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq931
    | (have j0 := eq931 X0 X1
       grind)
    | exact resolve eq931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq935 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq934
  have eq936 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq935
    | (have j0 := eq935 X0 X1
       grind)
    | exact resolve eq935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq8795 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq887
       grind)
    | exact superpose eq887 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq887
       grind)
    | exact resolve eq12 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq8801 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq8795
  have eq39536 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8801
       grind)
    | exact superpose eq8801 eq16
    | exact resolve eq16 eq8801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8801
  have eq39577 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39536
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq39536
    | exact resolve eq39536 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq39536
  have eq39588 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq39577
  have eq39589 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq39588
  have eq39607 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq39589
       grind)
    | exact superpose eq39589 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq39589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39631 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq39607
       have r₂ := eq296 x
       grind)
    | exact resolve eq39607 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39607
  have eq39634 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq39631
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq39631
    | exact resolve eq39631 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39631
  have eq39635 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq39634
       have i₂ := eq296 x
       grind)
    | exact superpose eq296 eq39634
    | exact resolve eq39634 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq39634
  have eq84297 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq39635
       grind)
    | exact superpose eq39635 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq39635
       grind)
    | exact resolve eq12 eq39635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39635
  have eq84328 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq84297
  have eq84351 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq84328
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq84328
    | exact resolve eq84328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84328
  have eq963102 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq39589
       have i₂ := eq84351
       grind)
    | exact superpose eq84351 eq39589
    | exact resolve eq39589 eq84351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39589 eq84351
  have eq963298 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq963102
  have eq963542 : (k x y) = (τ (σ (M.op x x))) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq963298
       grind)
    | exact superpose eq963298 eq10
    | exact resolve eq10 eq963298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963298
  have eq964060 : (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq963542
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq963542
    | exact resolve eq963542 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963542
  have eq964061 : (k x y) = (M.op x x) := by grind
  clear eq964060
  have eq964400 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq862 x y
       have i₂ := eq964061
       grind)
    | exact superpose eq964061 eq862
    | (have j0 := eq862 x y
       grind)
    | exact resolve eq862 eq964061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq964403 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq936 x y
       have i₂ := eq964061
       grind)
    | exact superpose eq964061 eq936
    | (have j0 := eq936 x y
       grind)
    | (have r₁ := eq936 x y
       have r₂ := eq964061
       grind)
    | exact resolve eq936 eq964061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq964061
  have eq964627 : (M.op x y) = (M.op x x) := by grind
  clear eq964403
  have eq964629 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq964400
  have eq965108 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq964629
       grind)
    | exact superpose eq964629 eq16
    | exact resolve eq16 eq964629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964629
  have eq965266 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq965108
       have i₂ := eq964627
       grind)
    | exact superpose eq964627 eq965108
    | exact resolve eq965108 eq964627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964627 eq965108
  have eq965267 : False := by grind
  exact eq965267

/-- `Equation4305`: `x ◇ (x ◇ y) = z ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pxy_pxy_pyx_Equation4305 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4305 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4305.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq23 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq27 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    grind
  clear eq27
  have eq740 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq709 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq748 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq740 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq740 X0 X1
       have r₂ := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq740 X0 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq740 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq770 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq748 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq748
    | exact resolve eq748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq805 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq770
    | (have j0 := eq770 X0 X1
       grind)
    | exact resolve eq770 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq829 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq805 X1 X0
       grind)
    | exact superpose eq805 eq10
    | (have j1 := eq805 X1 X0
       grind)
    | exact resolve eq10 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq862 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq959 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq862 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq977 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq959 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq959
    | (have j0 := eq959 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq959 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq959 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq959 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq959 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq959 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq977 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq985 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq979 X0 X1
       have j1 := eq959 X0 X1
       grind)
    | (have r₁ := eq979 X0 X1
       have r₂ := eq959 X0 X1
       grind)
    | (have r₁ := eq979 X1 X0
       have r₂ := eq959 X0 X1
       grind)
    | exact resolve eq979 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq990 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq978 X1
       grind)
    | exact superpose eq978 eq985
    | (have j0 := eq985 X0 X1
       grind)
    | exact resolve eq985 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1010 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq978 (σ X0)
       grind)
    | exact superpose eq978 eq15
    | exact resolve eq15 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq978 (τ X0)
       grind)
    | exact superpose eq978 eq35
    | exact resolve eq35 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1016 X0
       have i₂ := eq978 X0
       grind)
    | exact superpose eq978 eq1016
    | exact resolve eq1016 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1043 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1010 X0
       have i₂ := eq978 X0
       grind)
    | exact superpose eq978 eq1010
    | exact resolve eq1010 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1199 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (M.op (τ (M.op X0 X0)) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1204 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq1037 X0
       grind)
    | exact superpose eq1037 eq9
    | exact resolve eq9 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op X1 (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq1037 X0
       grind)
    | exact superpose eq1037 eq9
    | exact resolve eq9 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1214 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1199 X0
       have j1 := eq12 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq1199 X0
       have r₂ := eq12 (τ (M.op X0 X0)) (τ X0)
       grind)
    | (have r₁ := eq1199 X0
       have r₂ := eq12 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact resolve eq1199 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1225 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1214 X0
       have i₂ := eq35 (M.op X0 X0) X0
       grind)
    | exact superpose eq35 eq1214
    | exact resolve eq1214 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1214
  have eq1261 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1267 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq9
    | exact resolve eq9 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq9
    | exact resolve eq9 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1262 X0
       have j1 := eq12 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq1262 X0
       have r₂ := eq12 (σ (M.op X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq1262 X0
       have r₂ := eq12 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq1262 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1278 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1261 X0 X1
       have j1 := eq959 X1 (σ X0)
       grind)
    | (have r₁ := eq1261 X0 X1
       have r₂ := eq959 (σ X0) X1
       grind)
    | (have r₁ := eq1261 X0 X0
       have r₂ := eq959 X0 (σ X0)
       grind)
    | exact resolve eq1261 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1282 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1277 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1277
    | exact resolve eq1277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1402 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (τ X1))) = (M.op X2 (M.op X2 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1204 X1 X2
       have i₂ := eq1204 X1 X0
       grind)
    | exact superpose eq1204 eq1204
    | exact resolve eq1204 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1445 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1402 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1402
    | exact resolve eq1402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1494 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1445 (M.op X3 X1) X2 X3
       have i₂ := eq1445 X1 X3 X0
       grind)
    | (have i₁ := eq1445 (M.op X3 X1) X2 X3
       have i₂ := eq1445 X1 X0 X3
       grind)
    | exact superpose eq1445 eq1445
    | exact resolve eq1445 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1495 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1445 (M.op X3 X1) X2 X3
       have i₂ := eq9 X3 X1 X0
       grind)
    | (have i₁ := eq1445 (M.op X1 X2) X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1445
    | exact resolve eq1445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1499 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1445 (M.op X1 X3) X2 X3
       have i₂ := eq9 X0 X1 X3
       grind)
    | (have i₁ := eq1445 (M.op X0 X1) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1445
    | exact resolve eq1445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1525 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X2 X1) X3
       have i₂ := eq1445 X1 X2 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X2 X1) X3
       have i₂ := eq1445 X1 X0 X2
       grind)
    | exact superpose eq1445 eq9
    | exact resolve eq9 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (τ X1) X0)) = (M.op X2 (M.op (τ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1205 X1 X2
       have i₂ := eq1205 X1 X0
       grind)
    | exact superpose eq1205 eq1205
    | exact resolve eq1205 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1618 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1533 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1533
    | exact resolve eq1533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1769 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X3 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X2) X3
       have i₂ := eq1618 X1 X2 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X1 X2) X3
       have i₂ := eq1618 X1 X0 X2
       grind)
    | exact superpose eq1618 eq9
    | exact resolve eq9 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1784 : ∀ X0 : G, (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq1225 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1822 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq1784 X0
       have i₂ := eq1043 X0
       grind)
    | exact superpose eq1043 eq1784
    | exact resolve eq1784 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1832 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1822 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1822
    | exact resolve eq1822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq1838 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1832 X0
       have i₂ := eq23 (M.op X0 X0) (σ X0)
       grind)
    | exact superpose eq23 eq1832
    | exact resolve eq1832 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1832
  have eq1842 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1838 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1838
    | exact resolve eq1838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1844 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq1842 X0
       grind)
    | exact superpose eq1842 eq1225
    | exact resolve eq1225 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1845 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1282 X0
       have i₂ := eq1842 X0
       grind)
    | exact superpose eq1842 eq1282
    | exact resolve eq1282 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq1842
  have eq2436 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1278 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1278 X0 (σ X0)
       grind)
    | exact superpose eq1278 eq10
    | (have j1 := eq1278 X1 X0
       grind)
    | exact resolve eq10 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq3046 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2436 (σ X1) X0
       grind)
    | exact superpose eq2436 eq15
    | (have j1 := eq2436 (σ X1) X0
       grind)
    | exact resolve eq15 eq2436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq3075 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3046 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3046
    | (have j0 := eq3046 X0 X1
       grind)
    | exact resolve eq3046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3843 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3075 x y
       grind)
    | exact superpose eq3075 eq16
    | (have j1 := eq3075 x y
       grind)
    | exact resolve eq16 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3843
       have i₂ := eq990 y x
       grind)
    | exact superpose eq990 eq3843
    | (have j1 := eq990 y x
       grind)
    | exact resolve eq3843 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq3991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3980
  have eq3992 : y = (M.op x x) := by grind
  clear eq3991
  have eq4005 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0 x
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq990
    | (have j0 := eq990 X0 x
       grind)
    | exact resolve eq990 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq4010 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1267 x X0
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq1267
    | exact resolve eq1267 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq4011 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1268 x X0
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq1268
    | exact resolve eq1268 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq4030 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1445 x X0 x
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq1445
    | exact resolve eq1445 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4032 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1618 x X0 x
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq1618
    | exact resolve eq1618 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4074 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 x) X1
       have i₂ := eq4030 X0
       grind)
    | exact superpose eq4030 eq9
    | exact resolve eq9 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4077 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 x))) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1445 (M.op X1 x) X0 X1
       have i₂ := eq4030 X1
       grind)
    | exact superpose eq4030 eq1445
    | exact resolve eq1445 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4079 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1618 X1 X0 (M.op X1 x)
       have i₂ := eq4030 X1
       grind)
    | exact superpose eq4030 eq1618
    | exact resolve eq1618 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4084 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (M.op (τ X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1205 X0 (M.op (τ X0) x)
       have i₂ := eq4030 (τ X0)
       grind)
    | exact superpose eq4030 eq1205
    | exact resolve eq1205 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq4030
  have eq4087 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4032 (M.op x X1)
       have i₂ := eq1445 X1 x X0
       grind)
    | (have i₁ := eq4032 (M.op x X1)
       have i₂ := eq1445 X1 X0 x
       grind)
    | exact superpose eq1445 eq4032
    | exact resolve eq4032 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4088 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4032 (M.op x X1)
       have i₂ := eq9 x X1 X0
       grind)
    | (have i₁ := eq4032 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq4032
    | exact resolve eq4032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4093 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 x) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4032 (M.op X1 x)
       have i₂ := eq1618 X1 x X0
       grind)
    | (have i₁ := eq4032 (M.op X1 x)
       have i₂ := eq1618 X1 X0 x
       grind)
    | exact superpose eq1618 eq4032
    | exact resolve eq4032 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4118 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op x X0) X1
       have i₂ := eq4032 X0
       grind)
    | exact superpose eq4032 eq9
    | exact resolve eq9 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4121 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op X0 (M.op x X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1445 (M.op x X1) X0 X1
       have i₂ := eq4032 X1
       grind)
    | exact superpose eq4032 eq1445
    | exact resolve eq1445 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4143 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 x
       have i₂ := eq4005 (τ X0)
       grind)
    | exact superpose eq4005 eq19
    | (have j1 := eq4005 (τ X0)
       grind)
    | exact resolve eq19 eq4005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4005
  have eq4390 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ x)))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1445 (M.op X1 (σ x)) X0 X1
       have i₂ := eq4010 X1
       grind)
    | exact superpose eq4010 eq1445
    | exact resolve eq1445 eq4010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4563 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ X0) (σ (k X0 x))) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4011 (σ X0)
       have i₂ := eq3075 x X0
       grind)
    | exact superpose eq3075 eq4011
    | (have j1 := eq3075 x X0
       grind)
    | exact resolve eq4011 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq4644 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ X0) (σ (k X0 x))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4563 X0
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq4563
    | (have j0 := eq4563 X0
       grind)
    | exact resolve eq4563 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992 eq4563
  have eq5549 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4077 x X1
       have i₂ := eq1618 X1 x X0
       grind)
    | (have i₁ := eq4077 x X1
       have i₂ := eq1618 X1 X0 x
       grind)
    | exact superpose eq1618 eq4077
    | exact resolve eq4077 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5550 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4077 x X1
       have i₂ := eq9 X0 X1 x
       grind)
    | (have i₁ := eq4077 X0 X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq4077
    | exact resolve eq4077 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5551 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4077 x (M.op X0 x)
       have i₂ := eq4074 X0 x
       grind)
    | exact superpose eq4074 eq4077
    | exact resolve eq4077 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq5552 : (M.op (σ x) (M.op x y)) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4077 x (σ x)
       have i₂ := eq4011 x
       grind)
    | exact superpose eq4011 eq4077
    | exact resolve eq4077 eq4011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5598 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq4079 X0 X1
       have i₂ := eq5551 X1
       grind)
    | exact superpose eq5551 eq4079
    | exact resolve eq4079 eq5551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079
  have eq5634 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op x (M.op (τ X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4084 X0
       have i₂ := eq5551 (τ X0)
       grind)
    | exact superpose eq5551 eq4084
    | exact resolve eq4084 eq5551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084
  have eq5659 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X2 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4087 X2 (M.op X1 x)
       have i₂ := eq1618 X1 x X0
       grind)
    | (have i₁ := eq4087 X2 (M.op X1 x)
       have i₂ := eq1618 X1 X0 x
       grind)
    | exact superpose eq1618 eq4087
    | exact resolve eq4087 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5764 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x X1) X0)) = (M.op (M.op X2 (M.op X2 X1)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1618 (M.op x X1) X0 (M.op X2 (M.op X2 X1))
       have i₂ := eq4087 X2 X1
       grind)
    | exact superpose eq4087 eq1618
    | exact resolve eq1618 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087
  have eq5765 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) = (M.op (M.op X2 (M.op X2 X1)) (M.op x y)) := by
    intro X1 X2
    first
    | (have i₁ := eq5764 x X1 X2
       have i₂ := eq4118 X1 x
       grind)
    | exact superpose eq4118 eq5764
    | exact resolve eq5764 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5764
  have eq5793 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq5659 X0 X1 x
       have i₂ := eq4077 x X1
       grind)
    | exact superpose eq4077 eq5659
    | exact resolve eq5659 eq4077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077 eq5659
  have eq5930 : ∀ X0 X1 X2 : G, (M.op (M.op x X2) (M.op x y)) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1445 (M.op X1 (M.op X2 X1)) X0 (M.op x X2)
       have i₂ := eq4088 X1 X2
       grind)
    | exact superpose eq4088 eq1445
    | exact resolve eq1445 eq4088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq6105 : ∀ X0 X1 X2 : G, (M.op (M.op X2 x) (M.op x y)) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1445 (M.op X1 (M.op X2 X1)) X0 (M.op X2 x)
       have i₂ := eq4093 X1 X2
       grind)
    | exact superpose eq4093 eq1445
    | exact resolve eq1445 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093
  have eq6114 : ∀ X2 : G, (M.op (M.op X2 x) (M.op x y)) = (M.op (M.op x X2) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq6105 x x X2
       have i₂ := eq5930 x x X2
       grind)
    | exact superpose eq5930 eq6105
    | exact resolve eq6105 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq6146 : ∀ X2 : G, (M.op x (M.op X2 (M.op x y))) = (M.op (M.op x X2) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq6114 X2
       have i₂ := eq5551 X2
       grind)
    | exact superpose eq5551 eq6114
    | exact resolve eq6114 eq5551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq6171 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 (M.op x y))) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5930 X0 X1 X2
       have i₂ := eq6146 X2
       grind)
    | exact superpose eq6146 eq5930
    | exact resolve eq5930 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq7361 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5598 (M.op X0 (σ x)) X0
       have i₂ := eq4010 X0
       grind)
    | exact superpose eq4010 eq5598
    | exact resolve eq5598 eq4010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq8275 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op x y)) = (M.op x (M.op X2 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5550 X2 (M.op X2 X1)
       have i₂ := eq9 X2 X1 X0
       grind)
    | (have i₁ := eq5550 X2 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq5550
    | exact resolve eq5550 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8287 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op x y)) = (M.op x (M.op X2 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5550 X2 (M.op X1 X2)
       have i₂ := eq1618 X1 X2 X0
       grind)
    | (have i₁ := eq5550 X2 (M.op X1 X2)
       have i₂ := eq1618 X1 X0 X2
       grind)
    | exact superpose eq1618 eq5550
    | exact resolve eq5550 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8290 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op x y)) = (M.op x (M.op X1 (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5550 X1 (M.op (M.op x X0) X1)
       have i₂ := eq4118 X0 X1
       grind)
    | exact superpose eq4118 eq5550
    | exact resolve eq5550 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8411 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op x y)) = (M.op (M.op X1 X2) (M.op x y)) := by
    intro X1 X2
    first
    | (have i₁ := eq8275 x X1 X2
       have i₂ := eq8287 x X1 X2
       grind)
    | exact superpose eq8287 eq8275
    | exact resolve eq8275 eq8287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8275 eq8287
  have eq8604 : ∀ X0 : G, (σ (M.op x X0)) = (k (σ X0) (σ x)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4143 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4143
    | exact resolve eq4143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq8651 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq8604 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq8604
    | (have j0 := eq8604 X0
       grind)
    | exact resolve eq8604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8604
  have eq12210 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X1 (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1494 X3 X2 X2 X1
       have i₂ := eq1618 X1 X2 X0
       grind)
    | (have i₁ := eq1494 X3 X2 X2 X1
       have i₂ := eq1618 X1 X0 X2
       grind)
    | exact superpose eq1618 eq1494
    | exact resolve eq1494 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12211 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X1 (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1494 X3 X2 X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq1494 X0 X1 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1494
    | exact resolve eq1494 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12214 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op (M.op x X0) (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1494 X2 X1 X1 (M.op x X0)
       have i₂ := eq4118 X0 X1
       grind)
    | exact superpose eq4118 eq1494
    | exact resolve eq1494 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq12325 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op x (M.op X0 (M.op x y)))) = (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1494 x (M.op X3 (M.op X0 X3)) X1 X2
       have i₂ := eq5549 X3 X0
       grind)
    | exact superpose eq5549 eq1494
    | exact resolve eq1494 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12429 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op x y)) = (M.op x (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5550 X3 (M.op X3 (M.op X0 X2))
       have i₂ := eq1494 X1 X2 X3 X0
       grind)
    | (have i₁ := eq5550 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq1494 X0 X1 X2 X3
       grind)
    | exact superpose eq1494 eq5550
    | exact resolve eq5550 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq12945 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1495 X1 X0 X0 (σ x)
       have i₂ := eq4011 X0
       grind)
    | exact superpose eq4011 eq1495
    | exact resolve eq1495 eq4011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011
  have eq13152 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X3 (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1618 (M.op X0 X2) (M.op X0 X2) X3
       have i₂ := eq1495 X1 X2 (M.op X0 X2) X0
       grind)
    | (have i₁ := eq1618 X0 (M.op X1 X0) X2
       have i₂ := eq1495 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq1495 eq1618
    | exact resolve eq1618 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495 eq1618
  have eq14067 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2))))) = (M.op (M.op X3 (M.op X2 X0)) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5550 X3 (M.op X3 (M.op X2 X0))
       have i₂ := eq1499 X1 X2 X3 X0
       grind)
    | (have i₁ := eq5550 X3 (M.op X0 (M.op X0 X1))
       have i₂ := eq1499 X0 X1 X2 X3
       grind)
    | exact superpose eq1499 eq5550
    | exact resolve eq5550 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq14106 : ∀ X0 X2 X3 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op x y)) = (M.op (M.op X3 (M.op X2 X0)) (M.op x y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14067 X0 x X2 X3
       have i₂ := eq12429 X0 x X2 X3
       grind)
    | exact superpose eq12429 eq14067
    | exact resolve eq14067 eq12429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12429 eq14067
  have eq15738 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X2 X1) X3)) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1525 X2 X2 X1 X0
       have i₂ := eq1769 X2 X2 X1 X3
       grind)
    | exact superpose eq1769 eq1525
    | exact resolve eq1525 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq1769
  have eq19374 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 (M.op x y)))) = (M.op (M.op X1 (M.op x X0)) (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12210 X2 X3 (M.op X1 (M.op x X0)) X1
       have i₂ := eq4121 X1 X0
       grind)
    | exact superpose eq4121 eq12210
    | exact resolve eq12210 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210
  have eq35646 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5765 (M.op X0 X2) (M.op X0 X2)
       have i₂ := eq13152 X0 X1 X2 (M.op X0 X2)
       grind)
    | exact superpose eq13152 eq5765
    | exact resolve eq5765 eq13152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13152
  have eq35689 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op x y) (M.op X1 (M.op X1 X0))) ∨ (M.op X0 (M.op x y)) = (k (M.op X1 (M.op X1 X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x (M.op x X1)) (M.op x y)
       have i₂ := eq5765 X1 x
       grind)
    | exact superpose eq5765 eq12
    | exact resolve eq12 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35692 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op x y) (M.op X1 (M.op X1 X0))) ∨ (M.op X0 (M.op x y)) = (k (M.op x y) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq959 (M.op x y) (M.op x (M.op x X1))
       have i₂ := eq5765 X1 x
       grind)
    | exact superpose eq5765 eq959
    | exact resolve eq959 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq35778 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op y (M.op x y))) ∨ (M.op X0 (M.op x y)) = (k (M.op x y) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35692 X0 X1
       have i₂ := eq12214 y X0 X1
       grind)
    | exact superpose eq12214 eq35692
    | (have j0 := eq35692 X0 X1
       grind)
    | exact resolve eq35692 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35692
  have eq35781 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op y (M.op x y))) ∨ (M.op X0 (M.op x y)) = (k (M.op X1 (M.op X1 X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq35689 X0 X1
       have i₂ := eq12214 y X0 X1
       grind)
    | exact superpose eq12214 eq35689
    | (have j0 := eq35689 X0 X1
       grind)
    | exact resolve eq35689 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214 eq35689
  have eq35978 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k (M.op x y) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35778 X0 X1
       have i₂ := eq4032 y
       grind)
    | exact superpose eq4032 eq35778
    | (have j0 := eq35778 X0 X1
       grind)
    | exact resolve eq35778 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35778
  have eq35979 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k (M.op x y) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq35978 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35978
  have eq35984 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k (M.op X1 (M.op X1 X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq35781 X0 X1
       have i₂ := eq4032 y
       grind)
    | exact superpose eq4032 eq35781
    | (have j0 := eq35781 X0 X1
       grind)
    | exact resolve eq35781 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35781
  have eq35985 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (k (M.op X1 (M.op X1 X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq35984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35984
  have eq37199 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op (M.op X1 (M.op x y)) (M.op X0 (M.op X1 X0))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))
       have i₂ := eq5793 X0 X1
       grind)
    | exact superpose eq5793 eq12
    | exact resolve eq12 eq5793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq37297 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X1 (M.op X1 (M.op y (M.op x y)))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq37199 X0 X1
       have i₂ := eq19374 y X1 X0 X1
       grind)
    | exact superpose eq19374 eq37199
    | (have j0 := eq37199 X0 X1
       grind)
    | exact resolve eq37199 eq19374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19374 eq37199
  have eq37541 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x (M.op x (M.op x y))) ∨ (M.op x y) = (k (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq37297 X0 X1
       have i₂ := eq6171 X1 y x
       grind)
    | exact superpose eq6171 eq37297
    | (have j0 := eq37297 X0 X1
       grind)
    | exact resolve eq37297 eq6171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6171 eq37297
  have eq37654 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq37541 X0 X1
       have i₂ := eq4121 x y
       grind)
    | exact superpose eq4121 eq37541
    | (have j0 := eq37541 X0 X1
       grind)
    | exact resolve eq37541 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37541
  have eq37724 : ∀ X0 X1 : G, (M.op x y) = (k (M.op X0 (M.op X1 X0)) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have j0 := eq37654 X0 X1
       grind)
    | (have r₁ := eq37654 X0 X1
       have r₂ := eq4032 y
       grind)
    | exact resolve eq37654 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37654
  have eq38573 : (M.op (τ (M.op x (M.op y (M.op x y)))) (τ (M.op x y))) = (τ (M.op (M.op x (M.op y (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq1844 (M.op x y)
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq1844
    | exact resolve eq1844 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq38574 : (σ (M.op (M.op x (M.op y (M.op x y))) (M.op x y))) = (M.op (σ (M.op x (M.op y (M.op x y)))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1845 (M.op x y)
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq1845
    | exact resolve eq1845 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq38698 : (σ (M.op (M.op x (M.op x y)) (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38574
       have i₂ := eq5549 y x
       grind)
    | exact superpose eq5549 eq38574
    | exact resolve eq38574 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38574
  have eq38699 : (M.op (τ (M.op x (M.op y (M.op x y)))) (τ (M.op x y))) = (τ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq38573
       have i₂ := eq35646 x y x
       grind)
    | exact superpose eq35646 eq38573
    | exact resolve eq38573 eq35646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35646 eq38573
  have eq38863 : (M.op (σ (M.op x (M.op x y))) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq38698
       have i₂ := eq5765 y x
       grind)
    | exact superpose eq5765 eq38698
    | exact resolve eq38698 eq5765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5765 eq38698
  have eq38864 : (M.op (τ (M.op x (M.op y (M.op x y)))) (τ (M.op x y))) = (τ (M.op x (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq38699
       have i₂ := eq5551 x
       grind)
    | exact superpose eq5551 eq38699
    | exact resolve eq38699 eq5551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5551 eq38699
  have eq38996 : (σ (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38863
       have i₂ := eq4032 y
       grind)
    | exact superpose eq4032 eq38863
    | exact resolve eq38863 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38863
  have eq38997 : (M.op (τ (M.op x (M.op y (M.op x y)))) (τ (M.op x y))) = (τ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq38864
       have i₂ := eq4121 x y
       grind)
    | exact superpose eq4121 eq38864
    | exact resolve eq38864 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121 eq38864
  have eq39059 : (τ (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x y))) := by
    first
    | (have i₁ := eq38997
       have i₂ := eq4032 y
       grind)
    | exact superpose eq4032 eq38997
    | exact resolve eq38997 eq4032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032 eq38997
  have eq62334 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X2) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4390 (σ x) (M.op X2 X1)
       have i₂ := eq15738 X0 X1 X2 (σ x)
       grind)
    | (have i₁ := eq4390 (σ x) (M.op X2 X1)
       have i₂ := eq15738 (σ x) X2 X1 X0
       grind)
    | exact superpose eq15738 eq4390
    | exact resolve eq4390 eq15738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390 eq15738
  have eq62700 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op (σ x) (σ y))) = (M.op (M.op X1 X2) (M.op (σ x) (σ y))) := by
    intro X1 X2
    first
    | (have i₁ := eq62334 x X1 X2
       have i₂ := eq12945 (M.op X1 X2) x
       grind)
    | exact superpose eq12945 eq62334
    | exact resolve eq62334 eq12945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62334
  have eq64673 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ X0) (σ (M.op x X0))) ∨ y = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq4644 X0
       have i₂ := eq8651 X0
       grind)
    | exact superpose eq8651 eq4644
    | (have j0 := eq4644 X0
       have j1 := eq8651 X0
       grind)
    | exact resolve eq4644 eq8651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644 eq8651
  have eq64776 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ X0) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq64673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64673
  have eq66211 : (M.op (τ (M.op x y)) (τ (M.op x (M.op y (M.op x y))))) = (M.op x (M.op (τ (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq5634 (M.op x y)
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq5634
    | exact resolve eq5634 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5634
  have eq66626 : (M.op (τ (M.op x y)) (τ (M.op x (M.op x y)))) = (M.op x (M.op (τ (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq66211
       have i₂ := eq5549 y x
       grind)
    | exact superpose eq5549 eq66211
    | exact resolve eq66211 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66211
  have eq77765 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ (M.op x (M.op x y))) (σ (M.op x y)) X0
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq9
    | exact resolve eq9 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77791 : (M.op x (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq5549 (σ (M.op x y)) (σ (M.op x (M.op x y)))
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq5549
    | exact resolve eq5549 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77792 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op x (M.op (σ (M.op x (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq5550 (σ (M.op x (M.op x y))) (σ (M.op x y))
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq5550
    | exact resolve eq5550 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77817 : (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq12945 (σ (M.op x (M.op x y))) (σ (M.op x y))
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq12945
    | exact resolve eq12945 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq77833 : (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op x y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq35979 (σ (M.op x y)) (σ (M.op x (M.op x y)))
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq35979
    | exact resolve eq35979 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35979
  have eq77838 : (M.op x y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq37724 (σ (M.op x y)) (σ (M.op x (M.op x y)))
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq37724
    | exact resolve eq37724 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37724
  have eq77843 : (M.op x y) = (k (σ (M.op (M.op x y) (M.op x y))) (M.op (σ (M.op x (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq77838
       have i₂ := eq1043 (M.op x y)
       grind)
    | exact superpose eq1043 eq77838
    | exact resolve eq77838 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77838
  have eq77848 : (M.op (σ (M.op x y)) (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq77833
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq77833
    | exact resolve eq77833 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77833
  have eq77862 : (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq77817
       have i₂ := eq1043 (M.op x y)
       grind)
    | exact superpose eq1043 eq77817
    | exact resolve eq77817 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77817
  have eq77887 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq77792
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq77792
    | exact resolve eq77792 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77792
  have eq77888 : (M.op x (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op x (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq77791
       have i₂ := eq1043 (M.op x y)
       grind)
    | exact superpose eq1043 eq77791
    | exact resolve eq77791 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77791
  have eq77908 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq77765 X0
       have i₂ := eq38996
       grind)
    | exact superpose eq38996 eq77765
    | exact resolve eq77765 eq38996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38996 eq77765
  have eq77924 : (M.op x y) = (k (σ (M.op x (M.op y (M.op x y)))) (M.op (σ (M.op x (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq77843
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq77843
    | exact resolve eq77843 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77843
  have eq77937 : (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op x (M.op y (M.op x y))))) := by
    first
    | (have i₁ := eq77862
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq77862
    | exact resolve eq77862 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77862
  have eq77966 : (k (M.op x y) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq77848
       have i₂ := eq77887
       grind)
    | exact superpose eq77887 eq77848
    | exact resolve eq77848 eq77887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77848
  have eq77968 : (M.op x (σ (M.op x (M.op y (M.op x y))))) = (M.op (σ (M.op x (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq77888
       have i₂ := eq6146 y
       grind)
    | exact superpose eq6146 eq77888
    | exact resolve eq77888 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77888
  have eq77997 : (M.op x y) = (k (σ (M.op x (M.op x y))) (M.op (σ (M.op x (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq77924
       have i₂ := eq5549 y x
       grind)
    | exact superpose eq5549 eq77924
    | exact resolve eq77924 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77924
  have eq78010 : (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq77937
       have i₂ := eq5549 y x
       grind)
    | exact superpose eq5549 eq77937
    | exact resolve eq77937 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77937
  have eq78031 : (M.op x (σ (M.op x (M.op x y)))) = (M.op (σ (M.op x (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq77968
       have i₂ := eq5549 y x
       grind)
    | exact superpose eq5549 eq77968
    | exact resolve eq77968 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549 eq77968
  have eq78060 : (M.op x y) = (k (σ (M.op x (M.op x y))) (M.op x (σ (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq77997
       have i₂ := eq78031
       grind)
    | exact superpose eq78031 eq77997
    | exact resolve eq77997 eq78031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77997 eq78031
  have eq79214 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq77908 (M.op x y)
       have i₂ := eq77887
       grind)
    | exact superpose eq77887 eq77908
    | exact resolve eq77908 eq77887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77887
  have eq79674 : (k (τ (M.op x y)) (M.op x y)) = (τ (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq30 (M.op x y) (M.op x y)
       have i₂ := eq77966
       grind)
    | exact superpose eq77966 eq30
    | exact resolve eq30 eq77966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq77966
  have eq81069 : ∀ X0 : G, (M.op X0 (M.op (τ (M.op x y)) X0)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ (M.op x (M.op x y))) (τ (M.op x y)) X0
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq9
    | exact resolve eq9 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81080 : ∀ X0 : G, (M.op X0 (M.op X0 (τ (M.op x y)))) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1445 (τ (M.op x y)) X0 (τ (M.op x (M.op x y)))
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq1445
    | exact resolve eq1445 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq81096 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op x (M.op (τ (M.op x (M.op x y))) (τ (M.op x y)))) := by
    first
    | (have i₁ := eq5550 (τ (M.op x (M.op x y))) (τ (M.op x y))
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq5550
    | exact resolve eq5550 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5550
  have eq81108 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op (M.op (τ (M.op x y)) (τ (M.op x (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq8411 (τ (M.op x y)) (τ (M.op x (M.op x y)))
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq8411
    | exact resolve eq8411 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8411
  have eq81114 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op x (M.op x y))) (τ (M.op x y)))) = (M.op (τ (M.op x y)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12211 X0 X1 (τ (M.op x y)) (τ (M.op x (M.op x y)))
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq12211
    | exact resolve eq12211 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq81138 : (M.op (τ (M.op x y)) (M.op x y)) = (k (M.op (τ (M.op x (M.op x y))) (τ (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq35985 (τ (M.op x y)) (τ (M.op x (M.op x y)))
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq35985
    | exact resolve eq35985 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35985
  have eq81151 : (M.op (τ (M.op x y)) (M.op x y)) = (k (τ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq81138
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq81138
    | exact resolve eq81138 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81138
  have eq81173 : ∀ X0 X1 : G, (M.op X1 (τ (M.op x y))) = (M.op (τ (M.op x y)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq81114 X0 X1
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq81114
    | exact resolve eq81114 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81114
  have eq81179 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op (M.op x (M.op (τ (M.op x y)) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq81108
       have i₂ := eq66626
       grind)
    | exact superpose eq66626 eq81108
    | exact resolve eq81108 eq66626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66626 eq81108
  have eq81191 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op x (τ (M.op x y))) := by
    first
    | (have i₁ := eq81096
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq81096
    | exact resolve eq81096 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81096
  have eq81201 : ∀ X0 : G, (τ (M.op x y)) = (M.op X0 (M.op X0 (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq81080 X0
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq81080
    | exact resolve eq81080 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81080
  have eq81212 : ∀ X0 : G, (τ (M.op x y)) = (M.op X0 (M.op (τ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq81069 X0
       have i₂ := eq39059
       grind)
    | exact superpose eq39059 eq81069
    | exact resolve eq81069 eq39059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39059 eq81069
  have eq81238 : (M.op (τ (M.op x y)) (M.op x y)) = (τ (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq81151
       have i₂ := eq79674
       grind)
    | exact superpose eq79674 eq81151
    | exact resolve eq81151 eq79674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79674 eq81151
  have eq81264 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op (M.op x (M.op (M.op x y) (τ (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq81179
       have i₂ := eq14106 (τ (M.op x y)) (M.op x y) x
       grind)
    | (have i₁ := eq81179
       have i₂ := eq14106 (M.op x y) (τ (M.op x y)) x
       grind)
    | exact superpose eq14106 eq81179
    | exact resolve eq81179 eq14106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14106 eq81179
  have eq81317 : (τ (M.op x (σ (M.op x y)))) = (M.op x (τ (M.op x y))) := by
    first
    | (have i₁ := eq81238
       have i₂ := eq81191
       grind)
    | exact superpose eq81191 eq81238
    | exact resolve eq81238 eq81191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81238
  have eq81343 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op x (M.op (M.op (M.op x y) (τ (M.op x y))) (M.op x y))) := by
    first
    | (have i₁ := eq81264
       have i₂ := eq6146 (M.op (M.op x y) (τ (M.op x y)))
       grind)
    | exact superpose eq6146 eq81264
    | exact resolve eq81264 eq6146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81264
  have eq81381 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op x (M.op x (M.op (τ (M.op x y)) (M.op y (M.op x y))))) := by
    first
    | (have i₁ := eq81343
       have i₂ := eq8290 y (τ (M.op x y))
       grind)
    | exact superpose eq8290 eq81343
    | exact resolve eq81343 eq8290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8290 eq81343
  have eq81401 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op (τ (M.op x y)) (M.op x (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq81381
       have i₂ := eq12325 x x (τ (M.op x y)) y
       grind)
    | exact superpose eq12325 eq81381
    | exact resolve eq81381 eq12325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12325 eq81381
  have eq81412 : (M.op (τ (M.op x y)) (M.op x y)) = (M.op (M.op x y) (τ (M.op x y))) := by
    first
    | (have i₁ := eq81401
       have i₂ := eq81173 x (M.op x y)
       grind)
    | exact superpose eq81173 eq81401
    | exact resolve eq81401 eq81173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81173 eq81401
  have eq81422 : (M.op x (τ (M.op x y))) = (M.op (M.op x y) (τ (M.op x y))) := by
    first
    | (have i₁ := eq81412
       have i₂ := eq81191
       grind)
    | exact superpose eq81191 eq81412
    | exact resolve eq81412 eq81191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81191 eq81412
  have eq82638 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op (τ (M.op x y)) X0) (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq5598 (M.op (τ (M.op x y)) X0) X0
       have i₂ := eq81212 X0
       grind)
    | exact superpose eq81212 eq5598
    | exact resolve eq5598 eq81212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598 eq81212
  have eq83156 : (M.op x (σ (M.op x y))) = (σ (M.op x (τ (M.op x y)))) := by
    first
    | (have i₁ := eq11 (M.op x (σ (M.op x y)))
       have i₂ := eq81317
       grind)
    | exact superpose eq81317 eq11
    | exact resolve eq11 eq81317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81317
  have eq84995 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (M.op x y)))) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64776 (M.op (σ x) (σ y))
       have i₂ := eq5552
       grind)
    | exact superpose eq5552 eq64776
    | (have j0 := eq64776 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq64776 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552
  have eq85098 : (M.op (σ x) (σ y)) = (M.op (σ (τ (M.op x y))) (M.op x (σ (M.op x y)))) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq64776 (τ (M.op x y))
       have i₂ := eq83156
       grind)
    | exact superpose eq83156 eq64776
    | (have j0 := eq64776 (τ (M.op x y))
       grind)
    | exact resolve eq64776 eq83156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85140 : (σ (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77908 (σ (M.op x (M.op x y)))
       have i₂ := eq64776 (M.op x y)
       grind)
    | exact superpose eq64776 eq77908
    | (have j1 := eq64776 (M.op x y)
       grind)
    | exact resolve eq77908 eq64776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64776 eq77908
  have eq85255 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85140
       have i₂ := eq78010
       grind)
    | exact superpose eq78010 eq85140
    | exact resolve eq85140 eq78010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78010 eq85140
  have eq85271 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq85098
       have i₂ := eq11 (M.op x y)
       grind)
    | exact superpose eq11 eq85098
    | exact resolve eq85098 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85098
  have eq85327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op x y)) := by
    first
    | (have i₁ := eq85271
       have i₂ := eq79214
       grind)
    | exact superpose eq79214 eq85271
    | exact resolve eq85271 eq79214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79214 eq85271
  have eq85347 : y = (τ (M.op x y)) := by
    first
    | (have r₁ := eq85327
       have r₂ := eq16
       grind)
    | exact resolve eq85327 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85327
  have eq85443 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq81201 X0
       have i₂ := eq85347
       grind)
    | exact superpose eq85347 eq81201
    | exact resolve eq81201 eq85347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81201
  have eq85456 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq81422
       have i₂ := eq85347
       grind)
    | exact superpose eq85347 eq81422
    | exact resolve eq81422 eq85347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81422
  have eq85516 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq82638 X0
       have i₂ := eq85347
       grind)
    | exact superpose eq85347 eq82638
    | exact resolve eq82638 eq85347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82638
  have eq85543 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq83156
       have i₂ := eq85347
       grind)
    | exact superpose eq85347 eq83156
    | exact resolve eq83156 eq85347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83156 eq85347
  have eq85789 : ∀ X2 : G, (M.op (M.op x X2) (M.op x y)) = (M.op (M.op y X2) y) := by
    intro X2
    first
    | (have i₁ := eq6146 X2
       have i₂ := eq85516 X2
       grind)
    | exact superpose eq85516 eq6146
    | exact resolve eq6146 eq85516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6146
  have eq85801 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq7361 X0
       have i₂ := eq85516 X0
       grind)
    | exact superpose eq85516 eq7361
    | exact resolve eq7361 eq85516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361
  have eq86566 : (M.op x y) = (k (σ y) (M.op x (σ y))) := by
    first
    | (have i₁ := eq78060
       have i₂ := eq85443 x
       grind)
    | exact superpose eq85443 eq78060
    | exact resolve eq78060 eq85443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78060
  have eq86589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85255
       have i₂ := eq85443 x
       grind)
    | exact superpose eq85443 eq85255
    | exact resolve eq85255 eq85443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85255 eq85443
  have eq87140 : y = (M.op x y) := by
    first
    | (have r₁ := eq86589
       have r₂ := eq16
       grind)
    | exact resolve eq86589 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86589
  have eq87631 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq16
    | exact resolve eq16 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89221 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) y))) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84995
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq84995
    | exact resolve eq84995 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84995
  have eq89284 : y = (M.op y y) := by
    first
    | (have i₁ := eq85456
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq85456
    | exact resolve eq85456 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85456
  have eq89299 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq85516 X0
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq85516
    | exact resolve eq85516 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85516
  have eq89308 : (σ y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq85543
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq85543
    | exact resolve eq85543 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85543
  have eq89350 : ∀ X2 : G, (M.op (M.op y X2) y) = (M.op (M.op x X2) y) := by
    intro X2
    first
    | (have i₁ := eq85789 X2
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq85789
    | exact resolve eq85789 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85789
  have eq89466 : y = (k (σ y) (M.op x (σ y))) := by
    first
    | (have i₁ := eq86566
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq86566
    | exact resolve eq86566 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86566
  have eq89896 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq85801 X0
       have i₂ := eq89350 X0
       grind)
    | exact superpose eq89350 eq85801
    | exact resolve eq85801 eq89350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85801
  have eq90403 : y = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq89466
       have i₂ := eq89308
       grind)
    | exact superpose eq89308 eq89466
    | exact resolve eq89466 eq89308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89308 eq89466
  have eq90414 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq89299 X0
       have i₂ := eq89350 X0
       grind)
    | exact superpose eq89350 eq89299
    | exact resolve eq89299 eq89350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89299 eq89350
  have eq92693 : y = (σ (k y y)) := by
    first
    | (have i₁ := eq90403
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq90403
    | exact resolve eq90403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90403
  have eq92718 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq89896 X0
       have i₂ := eq90414 X0
       grind)
    | exact superpose eq90414 eq89896
    | exact resolve eq89896 eq90414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89896 eq90414
  have eq93686 : y = (σ (M.op y y)) := by
    first
    | (have i₁ := eq92693
       have i₂ := eq978 y
       grind)
    | exact superpose eq978 eq92693
    | exact resolve eq92693 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978 eq92693
  have eq93939 : y = (σ y) := by
    first
    | (have i₁ := eq93686
       have i₂ := eq89284
       grind)
    | exact superpose eq89284 eq93686
    | exact resolve eq93686 eq89284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93686
  have eq94672 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op (σ x) y)) = (M.op (M.op X1 X2) (M.op (σ x) y)) := by
    intro X1 X2
    first
    | (have i₁ := eq62700 X1 X2
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq62700
    | exact resolve eq62700 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62700
  have eq95208 : y ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq87631
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq87631
    | exact resolve eq87631 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87631
  have eq95369 : y = (M.op (σ x) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) y))) := by
    first
    | (have i₁ := eq89221
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq89221
    | exact resolve eq89221 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89221
  have eq95653 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) y)) := by
    intro X0
    first
    | (have i₁ := eq92718 X0
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq92718
    | exact resolve eq92718 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92718
  have eq95880 : (M.op (σ x) y) = (M.op (σ (M.op (σ x) y)) (σ (M.op (σ x) y))) ∨ y = (M.op (σ x) y) := by
    first
    | (have i₁ := eq95369
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq95369
    | exact resolve eq95369 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95369
  have eq96142 : (M.op (σ x) y) = (M.op (σ (M.op (σ x) y)) (σ (M.op (σ x) y))) := by
    first
    | (have r₁ := eq95880
       have r₂ := eq95208
       grind)
    | exact resolve eq95880 eq95208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95880
  have eq96244 : (M.op (σ x) y) = (σ (M.op (M.op (σ x) y) (M.op (σ x) y))) := by
    first
    | (have i₁ := eq96142
       have i₂ := eq1043 (M.op (σ x) y)
       grind)
    | exact superpose eq1043 eq96142
    | exact resolve eq96142 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq96142
  have eq96290 : (M.op (σ x) y) = (σ (M.op (M.op y (σ x)) (M.op (σ x) y))) := by
    first
    | (have i₁ := eq96244
       have i₂ := eq94672 y (σ x)
       grind)
    | (have i₁ := eq96244
       have i₂ := eq94672 (σ x) y
       grind)
    | exact superpose eq94672 eq96244
    | exact resolve eq96244 eq94672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94672 eq96244
  have eq97034 : (M.op (σ x) y) = (σ (M.op x (M.op y y))) := by
    first
    | (have i₁ := eq96290
       have i₂ := eq95653 y
       grind)
    | exact superpose eq95653 eq96290
    | exact resolve eq96290 eq95653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95653 eq96290
  have eq97208 : (σ (M.op x y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq97034
       have i₂ := eq89284
       grind)
    | exact superpose eq89284 eq97034
    | exact resolve eq97034 eq89284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89284 eq97034
  have eq97251 : (σ y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq97208
       have i₂ := eq87140
       grind)
    | exact superpose eq87140 eq97208
    | exact resolve eq97208 eq87140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87140 eq97208
  have eq97267 : y = (M.op (σ x) y) := by
    first
    | (have i₁ := eq97251
       have i₂ := eq93939
       grind)
    | exact superpose eq93939 eq97251
    | exact resolve eq97251 eq93939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93939 eq97251
  have eq97273 : False := by grind
  exact eq97273

/-- `Equation4413`: `x ◇ (x ◇ y) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation4413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4413.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X2) X2) := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X3) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X0) X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X1 X2) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X2) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 x X0 X3
       have i₂ := eq14 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X3 X0)
       have i₂ := eq14 X3 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X1 X3))) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X3
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq100 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq100
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq206 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq55 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ x)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 sF2)
       have i₂ := eq14 X0 X1 sF2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq14 X0 sF2 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X1) X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X0 X3))) = (M.op (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X3) X3
       have i₂ := eq52 X0 X3 X1
       grind)
    | (have i₁ := eq14 X2 (M.op X0 X3) X3
       have i₂ := eq52 X0 X1 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq57 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y X0
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq508 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op X2 X0) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 X2 X0 (M.op X2 X0) X3
       have i₂ := eq14 (M.op X2 X0) X0 X1
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X0) X2) X2) ∨ (M.op X3 (M.op (M.op X0 X1) X1)) = (k (M.op (M.op X0 X1) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq50 X0 X1 (M.op (M.op X0 X1) X1) X2
       grind)
    | exact superpose eq50 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X1) X3
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 : G, (M.op (M.op y X0) X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq413 x
       have i₂ := eq14 x y X0
       grind)
    | exact superpose eq14 eq413
    | (have j1 := eq14 x y X0
       grind)
    | exact resolve eq413 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq598 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) X1) X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq51
    | exact resolve eq51 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op y X0) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51
    | (have j0 := eq51 x y X0 X1
       grind)
    | exact resolve eq51 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op X0 (M.op X0 (σ x))) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (M.op X0 (M.op X0 sF2))
       have i₂ := eq51 X0 sF2 (M.op X0 (M.op X0 sF2)) x
       grind)
    | exact superpose eq51 eq211
    | exact resolve eq211 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq684 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1) := by
    intro X1
    first
    | exact superpose eq56 eq664
    | exact resolve eq664 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq802 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X2)) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op X2 X1) X3 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) (M.op X2 X1)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (M.op X0 (M.op (M.op x X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op x X1) X1)
       have i₂ := eq53 x X1 X0 (M.op (M.op x X1) X1)
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op sF2 X1) X1)
       have i₂ := eq53 sF2 X1 x (M.op (M.op sF2 X1) X1)
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq864 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq211 eq848
    | (have j0 := eq848 X0 (σ y)
       grind)
    | exact resolve eq848 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq848
  have eq865 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq846 X0 x
       have i₂ := eq206 x
       grind)
    | (have i₁ := eq846 X0 y
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq846
    | (have j0 := eq846 X0 y
       grind)
    | exact resolve eq846 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq846
  have eq932 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op x y) y))) = (M.op (M.op X2 (M.op X2 X1)) (M.op X1 x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 X1 X0 (M.op X1 x)
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X1 (M.op X1 X0)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1142 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op y (σ y)) (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq414 (M.op y sF3)
       have i₂ := eq552 sF3
       grind)
    | exact superpose eq552 eq414
    | exact resolve eq414 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq552
  have eq1448 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq864 eq52
    | exact resolve eq52 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq864
  have eq5311 : ∀ X0 : G, (M.op (M.op y (σ y)) (M.op x (M.op x y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq626 eq625
    | exact resolve eq625 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq626
  have eq5345 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq1142 eq5311
    | exact resolve eq5311 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq5311
  have eq7304 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq956
    | (have j0 := eq956 (σ y) (σ x)
       grind)
    | exact resolve eq956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq13942 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op X0 (σ x)) X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq210 (M.op x sF2) x
       have i₂ := eq366 (M.op x sF2) X1 (M.op x sF2) x
       grind)
    | exact superpose eq366 eq210
    | exact resolve eq210 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq366
  have eq14121 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq214 eq13942
    | exact resolve eq13942 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13942
  have eq14495 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op X0 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1)) := by
    intro X0 X1
    first
    | exact superpose eq14121 eq50
    | exact resolve eq50 eq14121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14121
  have eq14594 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq684 eq14495
    | exact resolve eq14495 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq14495
  have eq31107 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq5345 eq508
    | exact resolve eq508 eq5345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq5345
  have eq31578 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq7304 eq31107
    | exact resolve eq31107 eq7304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7304 eq31107
  have eq40195 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq865 eq802
    | exact resolve eq802 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq41032 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (M.op y (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq40195 X0
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq40195
    | exact resolve eq40195 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40195
  have eq71940 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X2 (M.op X2 X0))) := by
    intro X0 X2
    first
    | exact superpose eq214 eq598
    | exact resolve eq598 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq83609 : ∀ X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op X2 (M.op X2 X1)) (M.op X1 x)) := by
    intro X1 X2
    first
    | exact superpose eq865 eq932
    | exact resolve eq932 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq932
  have eq217178 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq16
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq217209 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq85 eq217178
    | exact resolve eq217178 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217178
  have eq217212 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq217209
       have r₂ := eq13 y x
       grind)
    | exact resolve eq217209 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217209
  have eq217213 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq217212
       grind)
    | exact superpose eq217212 eq74
    | exact resolve eq74 eq217212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223860 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq16
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq223893 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq223860
    | exact resolve eq223860 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223860
  have eq223896 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq223893
       have r₂ := eq13 x x
       grind)
    | exact resolve eq223893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223893
  have eq223898 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq223896
       grind)
    | exact superpose eq223896 eq43
    | exact resolve eq43 eq223896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487781 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92
    | (have j0 := eq92 x
       grind)
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq488075 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq487781
  have eq488256 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq488075
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq488075
    | exact resolve eq488075 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq488075
  have eq488347 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq488256
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq488256 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488256
  have eq488365 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq488347 eq49
    | exact resolve eq49 eq488347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq488385 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq488365
       have i₂ := eq223896
       grind)
    | exact superpose eq223896 eq488365
    | exact resolve eq488365 eq223896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223896 eq488365
  have eq488576 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93
    | (have j0 := eq93 y
       grind)
    | exact resolve eq93 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq488864 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq488576
  have eq489024 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq488864
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq488864
    | exact resolve eq488864 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq488864
  have eq489114 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq489024
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq489024 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489024
  have eq489153 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq489114 eq85
    | exact resolve eq85 eq489114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq489173 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq489153
       have i₂ := eq217212
       grind)
    | exact superpose eq217212 eq489153
    | exact resolve eq489153 eq217212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217212 eq489153
  have eq1444770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1444783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1444770
    | exact resolve eq1444770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444770
  have eq1444794 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1444783
       have r₂ := eq27
       grind)
    | exact resolve eq1444783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444783
  have eq1444806 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1444794 eq489173
    | exact resolve eq489173 eq1444794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489173 eq1444794
  have eq1445472 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1444806
    | exact resolve eq1444806 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1444806
  have eq1445473 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1445472
  have eq1445817 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1445473 eq488385
    | exact resolve eq488385 eq1445473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488385 eq1445473
  have eq1446511 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1445817
    | exact resolve eq1445817 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1445817
  have eq1446512 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq1446511
  have eq1446865 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq217213
       have i₂ := eq1446512
       grind)
    | exact superpose eq1446512 eq217213
    | exact resolve eq217213 eq1446512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217213
  have eq1446895 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1446512
       grind)
    | exact superpose eq1446512 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1446512
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1446512
       grind)
    | exact resolve eq13 eq1446512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446512
  have eq1447246 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1446895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446895
  have eq1447543 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq489114 eq1446865
    | exact resolve eq1446865 eq489114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489114 eq1446865
  have eq1447728 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1447543
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1447543
    | exact resolve eq1447543 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1447543
  have eq1448357 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1447728 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq1447728
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1447728
       grind)
    | exact resolve eq13 eq1447728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447728
  have eq1448708 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1448357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448357
  have eq1451892 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1447246 x
       grind)
    | exact superpose eq1447246 eq73
    | exact resolve eq73 eq1447246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1447246
  have eq1451925 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1451892
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1451892
    | exact resolve eq1451892 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451892
  have eq1451964 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1451925
    | exact resolve eq1451925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451925
  have eq1455181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1448708 eq1451964
    | exact resolve eq1451964 eq1448708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448708 eq1451964
  have eq1455193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1455181
  have eq1455204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1455193
    | exact resolve eq1455193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455193
  have eq1455230 : x = (M.op x x) := by
    first
    | (have r₁ := eq1455204
       have r₂ := eq27
       grind)
    | exact resolve eq1455204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455204
  have eq1455238 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq223898
       have i₂ := eq1455230
       grind)
    | exact superpose eq1455230 eq223898
    | exact resolve eq223898 eq1455230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223898
  have eq1455259 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq1455230
       grind)
    | exact superpose eq1455230 eq55
    | exact resolve eq55 eq1455230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1455295 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1455230
       grind)
    | exact superpose eq1455230 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1455230
       grind)
    | exact resolve eq13 eq1455230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1455648 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1455295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455295
  have eq1456016 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1455259
       have i₂ := eq1455230
       grind)
    | exact superpose eq1455230 eq1455259
    | exact resolve eq1455259 eq1455230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455230 eq1455259
  have eq1456037 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq488347 eq1455238
    | exact resolve eq1455238 eq488347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488347 eq1455238
  have eq1456302 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1456037
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1456037
    | exact resolve eq1456037 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1456037
  have eq1456573 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1456016 eq41032
    | exact resolve eq41032 eq1456016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41032
  have eq1457304 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1456573
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1456573
    | exact resolve eq1456573 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1456573
  have eq1457565 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1456302 eq56
    | exact resolve eq56 eq1456302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458304 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1456302 eq1457565
    | exact resolve eq1457565 eq1456302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457565
  have eq1460776 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1458304 eq31578
    | exact resolve eq31578 eq1458304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31578
  have eq1461487 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1460776
    | exact resolve eq1460776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1460776
  have eq1463692 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1455648 y
       grind)
    | exact superpose eq1455648 eq44
    | exact resolve eq44 eq1455648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1455648
  have eq1463719 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1463692
       have i₂ := eq1457304
       grind)
    | exact superpose eq1457304 eq1463692
    | exact resolve eq1463692 eq1457304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457304 eq1463692
  have eq1463763 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1463719
    | exact resolve eq1463719 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1463719
  have eq1463884 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1458304 eq1448
    | exact resolve eq1448 eq1458304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1466755 : (M.op (M.op x y) y) = (M.op (σ x) (M.op x (σ x))) := by
    first
    | (have i₁ := eq83609 x x
       have i₂ := eq1463884 x (M.op x x)
       grind)
    | exact superpose eq1463884 eq83609
    | (have j1 := eq1463884 x y
       grind)
    | exact resolve eq83609 eq1463884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83609 eq1463884
  have eq1468349 : x = (M.op (σ x) (M.op x (σ x))) := by
    first
    | exact superpose eq1456016 eq1466755
    | exact resolve eq1466755 eq1456016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456016 eq1466755
  have eq1471806 : ∀ X0 X1 : G, (M.op x (M.op x (σ x))) ≠ (M.op (M.op (M.op (M.op x (M.op x (σ x))) (σ x)) X0) X0) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1468349 eq530
    | exact resolve eq530 eq1468349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq1468349
  have eq1472268 : ∀ X1 : G, (M.op x (M.op x (σ x))) ≠ (M.op (M.op x (M.op x (σ x))) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq214 eq1471806
    | (have j0 := eq1471806 x X1
       grind)
    | exact resolve eq1471806 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq1471806
  have eq1472499 : ∀ X1 : G, (M.op x (M.op x (σ x))) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op x (M.op x (σ x)))) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq14594 eq1472268
    | (have j0 := eq1472268 X1
       grind)
    | exact resolve eq1472268 eq14594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14594 eq1472268
  have eq1472644 : ∀ X1 : G, (M.op x (M.op x (σ x))) ≠ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq71940 eq1472499
    | (have j0 := eq1472499 X1
       grind)
    | exact resolve eq1472499 eq71940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71940 eq1472499
  have eq1472718 : ∀ X1 : G, (M.op (σ x) (σ x)) ≠ (M.op x (M.op x (σ x))) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq1458304 eq1472644
    | (have j0 := eq1472644 X1
       grind)
    | exact resolve eq1472644 eq1458304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472644
  have eq1472747 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq56 eq1472718
    | (have j0 := eq1472718 X1
       grind)
    | exact resolve eq1472718 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472718
  have eq1472756 : ∀ X1 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | exact superpose eq1456302 eq1472747
    | (have j0 := eq1472747 X1
       grind)
    | exact resolve eq1472747 eq1456302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456302 eq1472747
  have eq1472760 : ∀ X1 : G, (M.op X1 (M.op x (M.op x (σ x)))) = (k (M.op x (M.op x (σ x))) X1) := by
    intro X1
    first
    | (have j0 := eq1472756 X1
       grind)
    | (have r₁ := eq1472756 X1
       have r₂ := eq1458304
       grind)
    | exact resolve eq1472756 eq1458304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472756
  have eq1472762 : ∀ X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X1
    first
    | exact superpose eq56 eq1472760
    | exact resolve eq1472760 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1472760
  have eq1472764 : ∀ X1 : G, (M.op X1 (σ x)) = (k (σ x) X1) := by
    intro X1
    first
    | exact superpose eq1458304 eq1472762
    | exact resolve eq1472762 eq1458304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458304 eq1472762
  have eq1479465 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1472764 eq1463763
    | exact resolve eq1463763 eq1472764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463763 eq1472764
  have eq1479466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1461487 eq1479465
    | exact resolve eq1479465 eq1461487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461487 eq1479465
  have eq1479545 : False := by grind
  exact eq1479545
