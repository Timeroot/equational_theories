import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pyx_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq76 (σ X0) (σ X1)
       grind)
    | exact superpose eq76 eq15
    | (have j1 := eq76 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq76 (τ X0) X1
       grind)
    | exact superpose eq76 eq18
    | (have j1 := eq76 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq76
  have eq189 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq189
    | (have j0 := eq189 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq727 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq769 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq727
       have i₂ := eq210 x y
       grind)
    | exact superpose eq210 eq727
    | (have j1 := eq210 (σ x) (σ y)
       grind)
    | (have r₁ := eq727
       have r₂ := eq210 x y
       grind)
    | (have r₁ := eq727
       have r₂ := eq210 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq727
       have r₂ := eq210 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq727 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq727
  have eq770 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq769
  have eq813 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq770
       grind)
    | exact superpose eq770 eq10
    | exact resolve eq10 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq844 : x = y ∨ x = y := by
    first
    | (have i₁ := eq813
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq813
    | exact resolve eq813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq845 : x = y := by grind
  clear eq844
  have eq847 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq845
       grind)
    | exact superpose eq845 eq16
    | exact resolve eq16 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq848 : False := by grind
  exact eq848

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq124 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq133 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq124
    | (have j0 := eq124 X0
       grind)
    | exact resolve eq124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq124
  have eq135 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133
    | (have j0 := eq133 X0
       grind)
    | exact resolve eq133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq136 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq135 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq135 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq135 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq143 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq136 (σ X0)
       grind)
    | exact superpose eq136 eq15
    | exact resolve eq15 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq143
    | exact resolve eq143 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq143
  have eq313 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq320 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq818 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq320 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq320
    | (have j0 := eq320 (τ X0) (τ X1)
       grind)
    | exact resolve eq320 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq825 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq818
    | (have j0 := eq818 X0 X1
       grind)
    | exact resolve eq818 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq828 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq830 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq831 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq830
    | (have j0 := eq830 X0 X1
       grind)
    | exact resolve eq830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq832 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq831 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq831
    | (have j0 := eq831 X0 X1
       grind)
    | exact resolve eq831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq833 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq832
    | (have j0 := eq832 X0 X1
       grind)
    | exact resolve eq832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq313
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq313
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq313
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq313
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq313 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq996 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq995
  have eq6940 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq16
    | exact resolve eq16 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq6941 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6940
       have r₂ := eq150 x
       grind)
    | exact resolve eq6940 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6940
  have eq6944 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6941
       grind)
    | exact superpose eq6941 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq6941
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6941
       grind)
    | exact resolve eq12 eq6941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6941
  have eq6962 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6944
  have eq6971 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq320 x y
       have i₂ := eq6962
       grind)
    | exact superpose eq6962 eq320
    | (have j0 := eq320 x y
       grind)
    | exact resolve eq320 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq6962
  have eq6978 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6971
  have eq6979 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6978
  have eq7038 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6979
       grind)
    | exact superpose eq6979 eq16
    | exact resolve eq16 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7047 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6979
       grind)
    | exact superpose eq6979 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6979
       grind)
    | exact resolve eq12 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6979
  have eq7066 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7047
  have eq7069 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq7066
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7066
    | exact resolve eq7066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7066
  have eq7315 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7069
       grind)
    | exact superpose eq7069 eq10
    | exact resolve eq10 eq7069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7069
  have eq7382 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq7315
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7315
    | exact resolve eq7315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7315
  have eq7394 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq16
    | exact resolve eq16 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7382
  have eq7395 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq7394
       have r₂ := eq150 x
       grind)
    | exact resolve eq7394 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7394
  have eq7635 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq7395
       grind)
    | exact superpose eq7395 eq10
    | exact resolve eq10 eq7395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7395
  have eq7707 : x = (k x y) := by
    first
    | (have i₁ := eq7635
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7635
    | exact resolve eq7635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7635
  have eq7732 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq833 x y
       have i₂ := eq7707
       grind)
    | exact superpose eq7707 eq833
    | (have j0 := eq833 x y
       grind)
    | (have r₁ := eq833 x y
       have r₂ := eq7707
       grind)
    | exact resolve eq833 eq7707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq7707
  have eq7736 : x = y ∨ x = (M.op x y) := by grind
  clear eq7732
  have eq7855 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7736
       grind)
    | exact superpose eq7736 eq16
    | exact resolve eq16 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7736
  have eq7860 : x = (M.op x y) := by
    first
    | (have r₁ := eq7855
       have r₂ := eq150 x
       grind)
    | exact resolve eq7855 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7855
  have eq7864 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7038
       have i₂ := eq7860
       grind)
    | exact superpose eq7860 eq7038
    | exact resolve eq7038 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038 eq7860
  have eq7888 : (σ x) = (σ y) := by grind
  clear eq7864
  have eq8022 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7888
       grind)
    | exact superpose eq7888 eq10
    | exact resolve eq10 eq7888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq8095 : x = y := by
    first
    | (have i₁ := eq8022
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8022
    | exact resolve eq8022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8022
  have eq8110 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq16
    | exact resolve eq16 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq8116 : False := by grind
  exact eq8116

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65
    | exact resolve eq65 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq265 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq241
  have eq270 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq265 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq265 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq265 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq265
  have eq274 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq270 (σ X0) X1
       grind)
    | exact superpose eq270 eq15
    | (have j1 := eq270 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq296 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq274 (τ X1) X0
       grind)
    | exact superpose eq274 eq19
    | (have j1 := eq274 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq274
  have eq405 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq296
    | exact resolve eq296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq433 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1060 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq16
    | (have j1 := eq283 x y
       grind)
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1060
       have i₂ := eq433 y x
       grind)
    | exact superpose eq433 eq1060
    | (have j1 := eq433 (σ x) (σ y)
       grind)
    | (have r₁ := eq1060
       have r₂ := eq433 y x
       grind)
    | (have r₁ := eq1060
       have r₂ := eq433 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1060
       have r₂ := eq433 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1060 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq1060
  have eq1090 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1089
  have eq1116 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1090
       grind)
    | exact superpose eq1090 eq10
    | exact resolve eq10 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1160 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1116
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1116
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1161 : x = y := by grind
  clear eq1160
  have eq1163 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1161
       grind)
    | exact superpose eq1161 eq16
    | exact resolve eq16 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1164 : False := by grind
  exact eq1164

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq3661 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq81 X1 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 (σ X1) X0
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq81 X0 (σ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3696 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq376308 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq3696 X1 X0
       grind)
    | exact superpose eq3696 eq11
    | (have j1 := eq3696 X1 X0
       grind)
    | exact resolve eq11 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq376537 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq376308 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq376308
    | (have j0 := eq376308 X0 X1
       grind)
    | exact resolve eq376308 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq376308
  have eq376538 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq376537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376537
  have eq377408 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376538 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq376538
    | exact resolve eq376538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq376538 X0 (σ X1)
       grind)
    | exact superpose eq376538 eq15
    | (have j1 := eq376538 X0 (σ X1)
       grind)
    | exact resolve eq15 eq376538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376538
  have eq378723 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq377408 (τ X0) X1
       grind)
    | exact superpose eq377408 eq17
    | (have j1 := eq377408 (τ X0) X1
       grind)
    | exact resolve eq17 eq377408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq377408
  have eq382381 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378723 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq378723
    | exact resolve eq378723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378723
  have eq383153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq382381 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq382381
    | (have j0 := eq382381 X0 X1
       grind)
    | exact resolve eq382381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382381
  have eq388258 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq377565 x y
       grind)
    | exact superpose eq377565 eq16
    | (have j1 := eq377565 x y
       grind)
    | exact resolve eq16 eq377565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388438 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq377565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377565
  have eq393844 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq388258
       have i₂ := eq383153 x y
       grind)
    | exact superpose eq383153 eq388258
    | (have j1 := eq383153 (σ x) (σ y)
       grind)
    | (have r₁ := eq388258
       have r₂ := eq383153 x y
       grind)
    | exact resolve eq388258 eq383153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393847 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq393844
  have eq393856 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq393847
       grind)
    | exact superpose eq393847 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq393847
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq393847
       grind)
    | exact resolve eq13 eq393847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393847
  have eq393924 : y = (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq393856
  have eq420349 : y ≠ y ∨ (M.op x y) = (k x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq393924
       grind)
    | exact superpose eq393924 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq393924
       grind)
    | exact resolve eq12 eq393924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393924
  have eq420418 : y = (k x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq420349
  have eq467644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq388438 x y
       have i₂ := eq420418
       grind)
    | exact superpose eq420418 eq388438
    | (have j0 := eq388438 x y
       grind)
    | exact resolve eq388438 eq420418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388438 eq420418
  have eq467662 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq467644
  have eq467663 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq467662
  have eq469413 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq388258
       have i₂ := eq467663
       grind)
    | exact superpose eq467663 eq388258
    | exact resolve eq388258 eq467663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388258 eq467663
  have eq469508 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq469413
  have eq469509 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq469508
  have eq469525 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq469509
       grind)
    | exact superpose eq469509 eq16
    | exact resolve eq16 eq469509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469588 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq469509
       grind)
    | exact superpose eq469509 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq469509
       grind)
    | exact resolve eq13 eq469509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469660 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq469588
  have eq469725 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq469660
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq469660
    | exact resolve eq469660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469660
  have eq532274 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq469725
       grind)
    | exact superpose eq469725 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq469725
       grind)
    | exact resolve eq12 eq469725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469725
  have eq532352 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq532274
  have eq532374 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq532352
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq532352
    | exact resolve eq532352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532352
  have eq532424 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq532374
       have i₂ := eq469509
       grind)
    | exact superpose eq469509 eq532374
    | exact resolve eq532374 eq469509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469509 eq532374
  have eq532425 : (σ y) = (σ (k x y)) := by grind
  clear eq532424
  have eq536582 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq383153 x y
       have i₂ := eq532425
       grind)
    | exact superpose eq532425 eq383153
    | (have j0 := eq383153 x y
       grind)
    | exact resolve eq383153 eq532425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383153 eq532425
  have eq537199 : y = (M.op x y) := by
    first
    | (have r₁ := eq536582
       have r₂ := eq469525
       grind)
    | exact resolve eq536582 eq469525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536582
  have eq541284 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq469525
       have i₂ := eq537199
       grind)
    | exact superpose eq537199 eq469525
    | exact resolve eq469525 eq537199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469525 eq537199
  have eq541363 : False := by grind
  exact eq541363

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq104
    | exact resolve eq104 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq108
    | exact resolve eq108 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq108
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq77
    | (have j0 := eq77 (σ x) (σ y)
       grind)
    | exact resolve eq77 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq97
  have eq793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq792
    | exact resolve eq792 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq796 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq793
       have r₂ := eq27
       grind)
    | exact resolve eq793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq798 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq796 eq53
    | exact resolve eq53 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq796 eq14
    | exact resolve eq14 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq800 eq51
    | exact resolve eq51 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq800 eq243
    | exact resolve eq243 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq946 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq929 eq53
    | exact resolve eq53 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq946
    | (have j0 := eq946 X0
       grind)
    | exact resolve eq946 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq955 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq934 eq929
    | exact resolve eq929 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq934
  have eq960 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by grind
  clear eq955
  have eq1019 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq951 eq798
    | exact resolve eq798 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq951
  have eq1026 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1019
  have eq1414 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq796 eq960
    | exact resolve eq960 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq960
  have eq1421 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1414
  have eq1449 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1421 eq1026
    | exact resolve eq1026 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1421
  have eq1482 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1449
  have eq1496 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq1482
       grind)
    | exact superpose eq1482 eq14
    | exact resolve eq14 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2767 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 (M.op y y)
       have i₂ := eq1496 y
       grind)
    | exact superpose eq1496 eq50
    | exact resolve eq50 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2774 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239 (M.op y y)
       have i₂ := eq1496 y
       grind)
    | exact superpose eq1496 eq239
    | exact resolve eq239 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3312 : x = (M.op y (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2774 eq2767
    | exact resolve eq2767 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767 eq2774
  have eq3318 : x = (M.op y (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3312
  have eq3791 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3318
       have i₂ := eq1482
       grind)
    | exact superpose eq1482 eq3318
    | exact resolve eq3318 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq3318
  have eq3802 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3791
  have eq3815 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq3802
       grind)
    | exact superpose eq3802 eq110
    | exact resolve eq110 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq3840 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1496 y
       have i₂ := eq3802
       grind)
    | exact superpose eq3802 eq1496
    | exact resolve eq1496 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496 eq3802
  have eq3849 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3840
  have eq3865 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3815
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3815
    | exact resolve eq3815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815
  have eq4277 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq3849
       grind)
    | exact superpose eq3849 eq72
    | exact resolve eq72 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3849
  have eq4315 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4277
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4277
    | exact resolve eq4277 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4277
  have eq4434 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3865 eq53
    | exact resolve eq53 eq3865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4449 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq4434
    | (have j0 := eq4434 X0
       grind)
    | exact resolve eq4434 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434
  have eq8052 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4315 eq4449
    | exact resolve eq4449 eq4315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315 eq4449
  have eq8092 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8052
  have eq8114 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8092 eq3865
    | exact resolve eq3865 eq8092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865 eq8092
  have eq8168 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8114
  have eq8177 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8168 eq27
    | exact resolve eq27 eq8168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq8178 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq8168 eq51
    | exact resolve eq51 eq8168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq8780 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq8178 x
       have i₂ := eq431 X0 sF2 x
       grind)
    | (have i₁ := eq8178 X0
       have i₂ := eq431 (M.op X0 X0) sF2 x
       grind)
    | exact superpose eq431 eq8178
    | exact resolve eq8178 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8813 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq8178 eq14
    | exact resolve eq14 eq8178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8814 : x = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq8178 eq50
    | exact resolve eq50 eq8178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq8824 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq8178 eq431
    | exact resolve eq431 eq8178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq8178
  have eq8868 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | exact superpose eq243 eq8824
    | exact resolve eq8824 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq8824
  have eq8883 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | exact superpose eq8168 eq8868
    | exact resolve eq8868 eq8168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8868
  have eq9217 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq8883 eq71
    | exact resolve eq71 eq8883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq8883
  have eq11135 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq8780 eq8813
    | exact resolve eq8813 eq8780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11433 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq11135
    | (have j0 := eq11135 (σ y)
       grind)
    | exact resolve eq11135 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq11467 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8168 eq11433
    | exact resolve eq11433 eq8168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168 eq11433
  have eq11549 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq11467 eq8780
    | exact resolve eq8780 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8780
  have eq11555 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq11467 eq9217
    | exact resolve eq9217 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9217 eq11467
  have eq11616 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq11555
    | exact resolve eq11555 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11555
  have eq11921 : (τ (σ x)) = (M.op y y) := by
    first
    | exact superpose eq11549 eq132
    | exact resolve eq132 eq11549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq11549
  have eq11947 : x = (M.op y y) := by
    first
    | exact superpose eq28 eq11921
    | exact resolve eq11921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11921
  have eq12636 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq239 y
       have i₂ := eq11947
       grind)
    | exact superpose eq11947 eq239
    | exact resolve eq239 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq12684 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq8813 y y
       have i₂ := eq11947
       grind)
    | exact superpose eq11947 eq8813
    | exact resolve eq8813 eq11947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8813 eq11947
  have eq12687 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq12684
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12684
    | exact resolve eq12684 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12684
  have eq12711 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq12636
       have i₂ := eq11616
       grind)
    | exact superpose eq11616 eq12636
    | exact resolve eq12636 eq11616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616 eq12636
  have eq13023 : (M.op x y) = (M.op (σ x) y) := by
    first
    | exact superpose eq12687 eq11135
    | exact resolve eq11135 eq12687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11135 eq12687
  have eq13060 : x = (M.op (σ x) y) := by
    first
    | exact superpose eq12711 eq8814
    | exact resolve eq8814 eq12711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8814 eq12711
  have eq13389 : x = (M.op x y) := by
    first
    | exact superpose eq13023 eq13060
    | exact resolve eq13060 eq13023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13023 eq13060
  have eq13390 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13389 eq20
    | exact resolve eq20 eq13389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13389
  have eq13456 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13390
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13390
    | exact resolve eq13390 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13390
  have eq13464 : False := by grind
  exact eq13464

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq669 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq674 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq669 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq669 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq669 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq669 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq675 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq657 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq657 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq683 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq674
    | (have j0 := eq674 X0 X1
       grind)
    | exact resolve eq674 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq684 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq683 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq686 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq691 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq686 X0 X1
       have j1 := eq684 X0 X1
       grind)
    | (have r₁ := eq686 X0 X1
       have r₂ := eq684 X0 X1
       grind)
    | exact resolve eq686 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq686
  have eq692 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq691
    | exact resolve eq691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691 x y
       grind)
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq833 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq692 X0 (τ X1)
       grind)
    | exact superpose eq692 eq18
    | exact resolve eq18 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq692
  have eq846 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq833
    | exact resolve eq833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq852 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq846
    | exact resolve eq846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq864 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq705
       have i₂ := eq852 x y
       grind)
    | exact superpose eq852 eq705
    | exact resolve eq705 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq852
  have eq865 : False := by grind
  exact eq865

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X1) X2 (M.op (M.op X1 X0) X1)
       have i₂ := eq9 X1 (M.op (M.op X1 X0) X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq54 (M.op (M.op X1 x) X1) (M.op X2 X2) X3
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X3 X3) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54 x X2 X3
       have i₂ := eq54 x X2 X0
       grind)
    | (have i₁ := eq54 x x X2
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X1) X2) = (M.op (M.op X2 X3) X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq54 X1 X2 x
       have i₂ := eq54 X3 X2 x
       grind)
    | (have i₁ := eq54 x x x
       have i₂ := eq54 x x X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X0 X0) X2)) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X3 x
       have i₂ := eq54 x X2 X0
       grind)
    | (have i₁ := eq9 x x x
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 X3) X2) X1) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X2 x X3
       have i₂ := eq54 X1 (M.op (M.op X2 X3) X2) x
       grind)
    | (have i₁ := eq9 x (M.op (M.op x X2) x) X2
       have i₂ := eq54 (M.op (M.op x X2) x) (M.op (M.op x X2) x) X2
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op X0 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 X2 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0) X3
       grind)
    | (have i₁ := eq54 X1 X2 (M.op X0 X0)
       have i₂ := eq60 X3 (M.op X0 X0) X0
       grind)
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq239 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 (M.op X0 X0))) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X1 (M.op X2 X2) X3
       have i₂ := eq55 (M.op X2 X2) X2 X3
       grind)
    | (have i₁ := eq55 X1 (M.op X2 X2) X3
       have i₂ := eq55 X1 X2 X2
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq55 X1 X0 x
       have i₂ := eq55 X3 X0 x
       grind)
    | (have i₁ := eq55 X1 x X3
       have i₂ := eq55 (M.op X3 X3) x X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op X1 (M.op X0 X0)) (M.op X3 (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X0 X0) X2
       have i₂ := eq55 X1 X0 X0
       grind)
    | (have i₁ := eq53 X0 (M.op X2 X2) X2
       have i₂ := eq55 (M.op X2 X2) X2 X3
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq239 X0 X1 X2 x
       have i₂ := eq53 X1 x X0
       grind)
    | exact superpose eq53 eq239
    | exact resolve eq239 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq239
  have eq380 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) ≠ X2 ∨ (M.op X2 X2) = (k (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq245 X0 X2 X1
       grind)
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq245 X0 X1 X2
       grind)
    | exact superpose eq245 eq12
    | (have j0 := eq12 (M.op X0 X0) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op x (M.op X0 X0))
       have r₂ := eq245 X0 (M.op x (M.op X0 X0)) x
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have r₂ := eq245 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact resolve eq12 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X2 (M.op X1 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 (M.op X1 X1)) X0
       have i₂ := eq306 X1 X2 X0
       grind)
    | exact superpose eq306 eq12
    | (have j0 := eq12 (M.op X2 (M.op X1 X1)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X0 X0)) (M.op X0 X0)
       have r₂ := eq306 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 X2) X1 X2
       have i₂ := eq54 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq54 eq68
    | exact resolve eq68 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq68
  have eq2892 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op X0 X1)) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1275 X3 X0 X1
       have i₂ := eq62 X1 X0 X2
       grind)
    | (have i₁ := eq1275 X3 X0 X1
       have i₂ := eq62 X2 X0 X1
       grind)
    | exact superpose eq62 eq1275
    | exact resolve eq1275 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1275
  have eq3988 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) (M.op (M.op X1 X4) X1)) = X1 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq2892 X1 X2 X4 (M.op x x)
       have i₂ := eq96 x X3 (M.op X1 X2) x
       grind)
    | (have i₁ := eq2892 x X1 X2 (M.op x X1)
       have i₂ := eq96 x (M.op x X1) (M.op x X1) X3
       grind)
    | exact superpose eq96 eq2892
    | exact resolve eq2892 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2892
  have eq5374 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X1 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq380 X1 X1 (M.op X0 (M.op X1 X1))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq5375 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5374 X0 X1
       have i₂ := eq291 X1 X0 X1 X0
       grind)
    | exact superpose eq291 eq5374
    | exact resolve eq5374 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq5374
  have eq5406 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5375 X0 (M.op X0 X0)
       have i₂ := eq245 X0 (M.op X0 X0) x
       grind)
    | (have i₁ := eq5375 X0 (M.op X0 X0)
       have i₂ := eq245 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq245 eq5375
    | exact resolve eq5375 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5375
  have eq5440 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5406 X0 X1 x
       have i₂ := eq306 X0 X1 x
       grind)
    | (have i₁ := eq5406 X0 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq306 (M.op X1 (M.op X0 X0)) X1 x
       grind)
    | exact superpose eq306 eq5406
    | exact resolve eq5406 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406
  have eq5531 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq451 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq25489 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 X2) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq1196 X0 X1
       grind)
    | exact superpose eq1196 eq9
    | (have j1 := eq1196 X0 X1
       grind)
    | exact resolve eq9 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25490 : ∀ X0 X1 : G, (σ X1) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq1196 X0 X1
       grind)
    | exact superpose eq1196 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq1196 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq1196 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq1196 X0 X1
       grind)
    | exact resolve eq12 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25558 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1196 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq25559 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25558
  have eq25562 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25490 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25490
  have eq25675 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25562 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25562
    | (have j0 := eq25562 X0 X1
       grind)
    | exact resolve eq25562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25562
  have eq25695 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25559 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq25559
    | (have j0 := eq25559 (τ X0)
       grind)
    | exact resolve eq25559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25699 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25695 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq25695
    | (have j0 := eq25695 X0
       grind)
    | exact resolve eq25695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25695
  have eq25700 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25699 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25699
    | (have j0 := eq25699 X0
       grind)
    | exact resolve eq25699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25699
  have eq25701 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25700 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25700
    | (have j0 := eq25700 X0
       grind)
    | exact resolve eq25700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25700
  have eq25711 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq25701 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq25701
    | (have j0 := eq25701 (τ X0)
       grind)
    | exact resolve eq25701 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25701
  have eq289474 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25675 (τ X1) (τ X0)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq25675
    | (have j0 := eq25675 X0 (τ X0)
       grind)
    | exact resolve eq25675 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25675
  have eq290500 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X1 X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq289474 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289474
    | (have j0 := eq289474 X0 X1
       grind)
    | exact resolve eq289474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289474
  have eq290526 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq290500 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq290500
    | (have j0 := eq290500 X0 X1
       grind)
    | exact resolve eq290500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290500
  have eq290546 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq290526 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290526
    | (have j0 := eq290526 X0 X1
       grind)
    | exact resolve eq290526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290526
  have eq290564 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X1 X0))) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq290546 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq290546
    | (have j0 := eq290546 X0 X1
       grind)
    | exact resolve eq290546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290546
  have eq290577 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq290564 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq290564
    | (have j0 := eq290564 X0 X1
       grind)
    | exact resolve eq290564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290564
  have eq290590 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq290577 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290577
    | (have j0 := eq290577 X0 X1
       grind)
    | exact resolve eq290577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290577
  have eq292148 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) ∨ (k X2 (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq290590 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq306 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq306 eq290590
    | (have j0 := eq290590 (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact resolve eq290590 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293388 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq290590 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290590
  have eq293460 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq292148 X0 X1 X2
       have i₂ := eq306 X1 X0 X2
       grind)
    | (have i₁ := eq292148 X0 X1 (M.op X0 (M.op X1 X1))
       have i₂ := eq306 (M.op X0 (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq306 eq292148
    | (have j0 := eq292148 X0 X1 X2
       grind)
    | exact resolve eq292148 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292148
  have eq293461 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq293460 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293460
  have eq294641 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (k X2 (M.op X3 (M.op X1 (M.op X0 X0)))) ∨ (M.op X1 (M.op X0 X0)) = (M.op X3 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq293461 X0 (M.op X2 X2) X2
       have i₂ := eq55 (M.op X2 X2) X2 X3
       grind)
    | (have i₁ := eq293461 X0 (M.op X2 X2) X2
       have i₂ := eq55 X1 X2 X2
       grind)
    | exact superpose eq55 eq293461
    | exact resolve eq293461 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq293461
  have eq295293 : ∀ X0 X1 X2 X3 : G, (k X2 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X1 (M.op X0 X0)) = (M.op X3 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq294641 X0 X1 X2 X3
       have i₂ := eq306 X0 X1 X3
       grind)
    | (have i₁ := eq294641 X0 X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq306 (M.op X1 (M.op X0 X0)) X1 X2
       grind)
    | exact superpose eq306 eq294641
    | (have j0 := eq294641 X0 X1 X2 X3
       grind)
    | exact resolve eq294641 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294641
  have eq295324 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq295293 X0 X1 X2 x
       have i₂ := eq306 X0 X1 x
       grind)
    | (have i₁ := eq295293 X0 X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq306 (M.op X1 (M.op X0 X0)) X1 X2
       grind)
    | exact superpose eq306 eq295293
    | (have j0 := eq295293 X0 X1 X2 x
       grind)
    | exact resolve eq295293 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295293
  have eq296004 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq245 X1 X3 X2
       have i₂ := eq295324 X1 X2 X0
       grind)
    | exact superpose eq295324 eq245
    | (have j1 := eq295324 X1 X3 X0
       grind)
    | exact resolve eq245 eq295324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq296799 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (k X2 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq295324 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295324
  have eq297201 : ∀ X0 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq296799 X2 X0 (M.op x (M.op X0 X0))
       have i₂ := eq5531 X0 x
       grind)
    | exact superpose eq5531 eq296799
    | (have j0 := eq296799 X2 X0 X2
       grind)
    | exact resolve eq296799 eq5531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531 eq296799
  have eq299532 : ∀ X0 X1 X3 : G, (M.op X3 X3) = (k (M.op X3 X3) (M.op X3 X3)) ∨ (M.op X1 (M.op X3 X3)) = (k X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq5440 X1 x
       have i₂ := eq296004 X0 X1 x X3
       grind)
    | exact superpose eq296004 eq5440
    | (have j1 := eq296004 X0 X3 x X1
       grind)
    | exact resolve eq5440 eq296004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440 eq296004
  have eq434920 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25489 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25489
    | exact resolve eq25489 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25489
  have eq436306 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k (σ X2) X0) ∨ (M.op (M.op X1 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq434920 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq434920
    | (have j0 := eq434920 X0 X1 X2
       grind)
    | exact resolve eq434920 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq434920
  have eq485824 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X1 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq436306 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq436306
    | (have j0 := eq436306 X1 X2 X2
       grind)
    | exact resolve eq436306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436306
  have eq488669 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X2)) = X2 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 (M.op X0 X0) X2 X3
       have i₂ := eq485824 X1 X0 X0
       grind)
    | exact superpose eq485824 eq64
    | (have j1 := eq485824 X1 X0 X2
       grind)
    | exact resolve eq64 eq485824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq485824
  have eq539029 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X3) X0)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3988 X0 X1 (M.op X0 X1) X3
       have i₂ := eq488669 X0 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq488669 eq3988
    | (have j1 := eq488669 X0 X2 X2 X3
       grind)
    | exact resolve eq3988 eq488669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988 eq488669
  have eq588679 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X4 X0)) = X0 ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq306 (M.op (M.op X0 X3) X0) x X2
       have i₂ := eq539029 X0 (M.op (M.op X0 X3) X0) X2 X3
       grind)
    | exact superpose eq539029 eq306
    | (have j1 := eq539029 X0 x X2 X3
       grind)
    | exact resolve eq306 eq539029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq539029
  have eq592898 : ∀ X0 X1 X2 X3 : G, X1 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X2 (M.op X0 X1)) = X1 ∨ (M.op X3 X1) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq588679 X0 X2 X3 x
       grind)
    | exact superpose eq588679 eq12
    | (have j1 := eq588679 X1 X3 X2 X0
       grind)
    | (have r₁ := eq12 (M.op x X0) X0
       have r₂ := eq588679 X0 X2 X0 x
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq588679 X0 X2 X3 x
       grind)
    | exact resolve eq12 eq588679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588679
  have eq593349 : ∀ X0 X1 X2 X3 : G, (k X1 X1) = X1 ∨ (M.op X2 (M.op X0 X1)) = X1 ∨ (M.op X3 X1) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq592898 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592898
  have eq596380 : ∀ X1 X2 X3 X4 : G, (k X2 X2) = X2 ∨ (M.op X4 X2) = (k X3 X2) ∨ (k X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq299532 x X1 (M.op x X1)
       have i₂ := eq593349 x X1 (M.op x X1) X3
       grind)
    | exact superpose eq593349 eq299532
    | (have j1 := eq593349 x X2 X2 X1
       grind)
    | exact resolve eq299532 eq593349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299532 eq593349
  have eq597580 : ∀ X1 X2 X3 X4 : G, (k X2 X2) = X2 ∨ (M.op X4 X2) = (k X3 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2 X3 X4
    first
    | (have j0 := eq596380 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596380
  have eq605613 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq597580 X0 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597580
  have eq615854 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq605613 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605613
  have eq616108 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25711 X0
       have i₂ := eq615854 X0 X1
       grind)
    | exact superpose eq615854 eq25711
    | (have j0 := eq25711 X0
       have j1 := eq615854 X0 X1
       grind)
    | exact resolve eq25711 eq615854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25711
  have eq616303 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq293388 X0 X0
       have i₂ := eq615854 X0 X1
       grind)
    | exact superpose eq615854 eq293388
    | (have j0 := eq293388 X0 X1
       have j1 := eq615854 X0 X1
       grind)
    | (have r₁ := eq293388 X0 X0
       have r₂ := eq615854 X0 X1
       grind)
    | exact resolve eq293388 eq615854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293388
  have eq616706 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq615854 X0 (τ X1)
       grind)
    | exact superpose eq615854 eq17
    | (have j1 := eq615854 X0 X1
       grind)
    | exact resolve eq17 eq615854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq615854
  have eq616779 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq616303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616303
  have eq616780 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq616779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616779
  have eq616817 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq616108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616108
  have eq632137 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq616706 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq616706
    | (have j0 := eq616706 X1 X1
       grind)
    | exact resolve eq616706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616706
  have eq632989 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632137 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq632137
    | (have j0 := eq632137 X0 X1
       grind)
    | exact resolve eq632137 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632137
  have eq633565 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616780 X1 X1
       have i₂ := eq632989 X0 X1
       grind)
    | exact superpose eq632989 eq616780
    | (have j0 := eq616780 X1 X1
       have j1 := eq632989 X0 X1
       grind)
    | exact resolve eq616780 eq632989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616780 eq632989
  have eq633629 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq633565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633565
  have eq635540 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq616817 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq616817
    | (have j0 := eq616817 (σ X0) X1
       grind)
    | exact resolve eq616817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616817
  have eq637257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq635540 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq635540
    | (have j0 := eq635540 X1 X1
       grind)
    | exact resolve eq635540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635540
  have eq647344 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq637257 x y
       grind)
    | exact superpose eq637257 eq16
    | (have j1 := eq637257 x y
       grind)
    | exact resolve eq16 eq637257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637257
  have eq649438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq647344
       have i₂ := eq633629 x y
       grind)
    | exact superpose eq633629 eq647344
    | (have j1 := eq633629 x y
       grind)
    | (have r₁ := eq647344
       have r₂ := eq633629 x y
       grind)
    | exact resolve eq647344 eq633629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633629 eq647344
  have eq649439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq649438
  have eq649440 : y = (M.op y y) := by grind
  clear eq649439
  have eq649780 : ∀ X0 : G, y ≠ (M.op y y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq297201 y x
       have i₂ := eq649440
       grind)
    | exact superpose eq649440 eq297201
    | exact resolve eq297201 eq649440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649847 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq649440
       grind)
    | exact superpose eq649440 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq649440
       grind)
    | exact resolve eq12 eq649440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650033 : y = (k y y) := by grind
  clear eq649847
  have eq650120 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq649780 X0
       have i₂ := eq649440
       grind)
    | exact superpose eq649440 eq649780
    | (have j0 := eq649780 X0
       grind)
    | (have r₁ := eq649780 X0
       have r₂ := eq649440
       grind)
    | exact resolve eq649780 eq649440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649440 eq649780
  have eq650121 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq650120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650120
  have eq650156 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25559 y
       have i₂ := eq650033
       grind)
    | exact superpose eq650033 eq25559
    | (have j0 := eq25559 y
       grind)
    | exact resolve eq25559 eq650033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25559 eq650033
  have eq650358 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq650156
  have eq654335 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq297201 (σ y) x
       have i₂ := eq650358
       grind)
    | exact superpose eq650358 eq297201
    | exact resolve eq297201 eq650358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297201
  have eq654763 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq654335 X0
       have i₂ := eq650358
       grind)
    | exact superpose eq650358 eq654335
    | (have j0 := eq654335 X0
       grind)
    | (have r₁ := eq654335 X0
       have r₂ := eq650358
       grind)
    | exact resolve eq654335 eq650358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650358 eq654335
  have eq654764 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq654763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654763
  have eq655766 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654764 (σ x)
       grind)
    | exact superpose eq654764 eq16
    | exact resolve eq16 eq654764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654764
  have eq655824 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq655766
       have i₂ := eq650121 x
       grind)
    | exact superpose eq650121 eq655766
    | exact resolve eq655766 eq650121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650121 eq655766
  have eq655825 : False := by grind
  exact eq655825

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq207 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq356 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq358 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq54 X0 x X1
       grind)
    | (have i₁ := eq54 X2 X2 X2
       have i₂ := eq54 X2 X1 X2
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq54 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq54 X0 X0 X2
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq210 sF2
       have i₂ := eq54 sF2 x sF2
       grind)
    | (have i₁ := eq210 x
       have i₂ := eq54 sF2 x x
       grind)
    | exact superpose eq54 eq210
    | exact resolve eq210 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq398 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq407 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq53 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq53 eq398
    | exact resolve eq398 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq569 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq826 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq355 sF0
       have i₂ := eq54 sF0 x x
       grind)
    | exact superpose eq54 eq355
    | exact resolve eq355 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq839 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq356 sF4
       have i₂ := eq54 sF4 x sF2
       grind)
    | exact superpose eq54 eq356
    | exact resolve eq356 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1038 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq826 eq54
    | exact resolve eq54 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1042 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1038 X0 x
       have i₂ := eq359 X0 sF0 x
       grind)
    | exact superpose eq359 eq1038
    | exact resolve eq1038 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1079 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq344 X3 X1 x
       have i₂ := eq344 X0 X1 x
       grind)
    | (have i₁ := eq344 X0 X1 X3
       have i₂ := eq344 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq344 eq344
    | exact resolve eq344 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq344 X0 (M.op X1 X1) X3
       have i₂ := eq344 X0 X1 X1
       grind)
    | (have i₁ := eq344 X0 (M.op X1 X1) X3
       have i₂ := eq344 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq344 eq344
    | exact resolve eq344 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq207 (M.op X1 X1)
       have i₂ := eq344 X0 X1 X1
       grind)
    | (have i₁ := eq207 (M.op X1 X1)
       have i₂ := eq344 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq344 eq207
    | exact resolve eq207 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1131 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1042 (M.op X1 X1)
       have i₂ := eq344 X0 X1 X1
       grind)
    | (have i₁ := eq1042 (M.op X1 X1)
       have i₂ := eq344 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq344 eq1042
    | exact resolve eq1042 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq1042
  have eq1175 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1090 X0 X1 x X3
       have i₂ := eq53 X0 x X1
       grind)
    | exact superpose eq53 eq1090
    | exact resolve eq1090 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1090
  have eq1192 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq839 eq54
    | exact resolve eq54 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq839
  have eq1196 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1192 X0 x
       have i₂ := eq359 X0 sF4 x
       grind)
    | exact superpose eq359 eq1192
    | exact resolve eq1192 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq1192
  have eq1204 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1196 sF4
       have i₂ := eq358 sF4 x sF4
       grind)
    | (have i₁ := eq1196 sF4
       have i₂ := eq358 sF4 sF4 x
       grind)
    | exact superpose eq358 eq1196
    | exact resolve eq1196 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq1196
  have eq12634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12634
    | exact resolve eq12634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12634
  have eq12646 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12635
       have r₂ := eq28
       grind)
    | exact resolve eq12635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12635
  have eq12648 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12646
    | exact resolve eq12646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12646
  have eq12651 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq12648
  have eq12707 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12651
    | exact resolve eq12651 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651
  have eq12713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12707 eq91
    | exact resolve eq91 eq12707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12707
  have eq12725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12713
  have eq12727 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12725
       have r₂ := eq28
       grind)
    | exact resolve eq12725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12725
  have eq12842 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12727
  have eq12898 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12842
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12842
    | exact resolve eq12842 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12842
  have eq12900 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12898
       grind)
    | exact superpose eq12898 eq45
    | exact resolve eq45 eq12898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898
  have eq12922 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12900
    | exact resolve eq12900 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12900
  have eq13079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12922 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13079
    | exact resolve eq13079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13079
  have eq13093 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13082
       have r₂ := eq28
       grind)
    | exact resolve eq13082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13082
  have eq13095 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13093
    | exact resolve eq13093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13093
  have eq13096 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13095
  have eq13100 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13096
  have eq13156 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13100
    | exact resolve eq13100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13100
  have eq13284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13156 eq12922
    | exact resolve eq12922 eq13156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12922 eq13156
  have eq13290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13284
  have eq13294 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13290
       have r₂ := eq28
       grind)
    | exact resolve eq13290 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13290
  have eq13296 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13294 eq28
    | exact resolve eq28 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13306 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13294 eq1204
    | exact resolve eq1204 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq13308 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq380 eq13306
    | (have j0 := eq13306 (σ y)
       grind)
    | exact resolve eq13306 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq13306
  have eq13427 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13294 eq13308
    | exact resolve eq13308 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13308
  have eq13441 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq13427
  have eq13522 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13441
       have i₂ := eq1079 sF2 sF2 x
       grind)
    | (have i₁ := eq13441
       have i₂ := eq1079 X0 sF2 sF2
       grind)
    | exact superpose eq1079 eq13441
    | exact resolve eq13441 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13533 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13441 eq1175
    | exact resolve eq1175 eq13441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441
  have eq13806 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f13806_12 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f13806_17 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f13806_19 : X0 ≠ (M.op (σ x) (M.op (M.op X0 X1) X0)) := by grind
    have f13806_20 : x ≠ (M.op x y) := by grind
    have f13806_22 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f13806_12 X0
         grind)
      | (have r₁ := f13806_12 X0
         have r₂ := f13806_20
         grind)
      | exact resolve f13806_12 f13806_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13806_23 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f13806_17 X0 (M.op (σ x) (σ x)) X1
         have i₂ := f13806_22 (M.op (σ x) (σ x))
         grind)
      | exact superpose f13806_22 f13806_17
      | exact resolve f13806_17 f13806_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13806_34 : X0 ≠ X0 := by
      first
      | (have i₁ := f13806_19
         have i₂ := f13806_23 X0 X1
         grind)
      | exact superpose f13806_23 f13806_19
      | (have r₁ := f13806_19
         have r₂ := f13806_23 X0 X1
         grind)
      | exact resolve f13806_19 f13806_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13806_36 : False := by grind
    exact f13806_36
  have eq13830 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13522 eq407
    | exact resolve eq407 eq13522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14651 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13533 eq13830
    | exact resolve eq13830 eq13533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533 eq13830
  have eq14662 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14651
  have eq15259 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f15259_12 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f15259_13 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f15259_20 : X0 ≠ (M.op (σ x) (M.op (σ x) X0)) := by grind
    have f15259_22 : x ≠ (M.op x y) := by grind
    have f15259_24 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f15259_13 X0
         grind)
      | (have r₁ := f15259_13 X0
         have r₂ := f15259_22
         grind)
      | exact resolve f15259_13 f15259_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15259_25 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f15259_12 X0 X1
         grind)
      | (have r₁ := f15259_12 X0 X1
         have r₂ := f15259_22
         grind)
      | exact resolve f15259_12 f15259_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15259_26 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f15259_25 X0 (M.op (σ x) (σ x))
         have i₂ := f15259_24 X0
         grind)
      | exact superpose f15259_24 f15259_25
      | exact resolve f15259_25 f15259_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15259_38 : X0 ≠ X0 := by
      first
      | (have i₁ := f15259_20
         have i₂ := f15259_26 X0
         grind)
      | exact superpose f15259_26 f15259_20
      | (have r₁ := f15259_20
         have r₂ := f15259_26 X0
         grind)
      | exact resolve f15259_20 f15259_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15259_41 : False := by grind
    exact f15259_41
  clear eq13522 eq13806
  have eq15406 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq15428 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq15406
    | (have j0 := eq15406 (σ y)
       grind)
    | exact resolve eq15406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15406
  have eq15475 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13294 eq15428
    | exact resolve eq15428 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13294 eq15428
  have eq15493 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15475
  have eq15505 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15493 eq14662
    | exact resolve eq14662 eq15493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14662 eq15493
  have eq15561 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15505
  have eq15814 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15561 eq58
    | exact resolve eq58 eq15561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq15815 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15561 eq91
    | exact resolve eq91 eq15561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq15561
  have eq15836 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq15815
  have eq15849 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15836
       have r₂ := eq13296
       grind)
    | exact resolve eq15836 eq13296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13296 eq15836
  have eq15850 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq15814
    | exact resolve eq15814 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15814
  have eq15890 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq15849
  have eq15949 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15890
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15890
    | exact resolve eq15890 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15890
  have eq16017 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15850
       have i₂ := eq15949
       grind)
    | exact superpose eq15949 eq15850
    | exact resolve eq15850 eq15949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15850 eq15949
  have eq16023 : x = (M.op x y) := by grind
  clear eq16017
  have eq16158 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16023 eq21
    | exact resolve eq21 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq16219 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq16023 eq1131
    | exact resolve eq1131 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq16221 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq16219 x x
       have i₂ := eq1124 x x
       grind)
    | exact superpose eq1124 eq16219
    | exact resolve eq16219 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq16219
  have eq16276 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16158
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16158
    | exact resolve eq16158 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158
  have eq16277 : x = (M.op x (M.op x x)) := by
    first
    | exact superpose eq16023 eq16221
    | exact resolve eq16221 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16221
  have eq16282 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16276 eq27
    | exact resolve eq27 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16687 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq16277
       have i₂ := eq1079 x x X0
       grind)
    | (have i₁ := eq16277
       have i₂ := eq1079 X0 x x
       grind)
    | exact superpose eq1079 eq16277
    | exact resolve eq16277 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq16277
  have eq16754 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op x x) X1
       have i₂ := eq16687 (M.op x x)
       grind)
    | exact superpose eq16687 eq14
    | exact resolve eq14 eq16687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16778 : x = (k x (M.op x x)) := by
    first
    | (have i₁ := eq407 (M.op x x)
       have i₂ := eq16687 (M.op x x)
       grind)
    | exact superpose eq16687 eq407
    | exact resolve eq407 eq16687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq16791 : ∀ X0 X1 : G, x = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 (M.op x x) x
       have i₂ := eq16687 (M.op x x)
       grind)
    | exact superpose eq16687 eq1175
    | exact resolve eq1175 eq16687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq16687
  have eq19340 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16754 X0 (M.op x x)
       have i₂ := eq16791 X0 x
       grind)
    | exact superpose eq16791 eq16754
    | exact resolve eq16754 eq16791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16754 eq16791
  have eq19556 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq19340 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19340
    | (have j0 := eq19340 y
       grind)
    | exact resolve eq19340 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19340
  have eq19612 : y = (M.op x x) := by
    first
    | exact superpose eq16023 eq19556
    | exact resolve eq19556 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023 eq19556
  have eq19621 : x = (k x y) := by
    first
    | (have i₁ := eq16778
       have i₂ := eq19612
       grind)
    | exact superpose eq19612 eq16778
    | exact resolve eq16778 eq19612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16778 eq19612
  have eq19895 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19621
       grind)
    | exact superpose eq19621 eq45
    | exact resolve eq45 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq19909 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq569 x y
       have i₂ := eq19621
       grind)
    | exact superpose eq19621 eq569
    | (have j0 := eq569 x y
       grind)
    | exact resolve eq569 eq19621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq19621
  have eq19912 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq19909
  have eq19920 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19912
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19912
    | exact resolve eq19912 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq19932 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16276 eq19895
    | exact resolve eq19895 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19895
  have eq19934 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19920
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19920
    | exact resolve eq19920 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19920
  have eq19946 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq19932
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19932
    | exact resolve eq19932 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19932
  have eq19947 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq19934
    | exact resolve eq19934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19934
  have eq19955 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16276 eq19946
    | exact resolve eq19946 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19946
  have eq19956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16276 eq19947
    | exact resolve eq19947 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19947
  have eq19960 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq19956
       have r₂ := eq28
       grind)
    | exact resolve eq19956 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19956
  have eq19964 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19960
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19960
    | exact resolve eq19960 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19960
  have eq19968 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19964
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19964
    | exact resolve eq19964 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19964
  have eq19971 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16276 eq19968
    | exact resolve eq19968 eq16276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16276 eq19968
  have eq20237 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq19971
  have eq20309 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16282 eq20237
    | exact resolve eq20237 eq16282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16282 eq20237
  have eq20316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19955 eq20309
    | exact resolve eq20309 eq19955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19955 eq20309
  have eq20318 : False := by grind
  exact eq20318
