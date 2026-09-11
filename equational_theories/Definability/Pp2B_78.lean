import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_pyy_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) x
       have i₂ := eq9 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq180 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | (have j1 := eq34 (σ X0)
       grind)
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq845 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq848 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq845 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq845 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq845 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq845 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq2838 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq848 (τ X0) X1
       grind)
    | exact superpose eq848 eq17
    | (have j1 := eq848 X0 X1
       grind)
    | exact resolve eq17 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2860 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq848 X2 X0
       grind)
    | exact superpose eq848 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq848 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq848 X0 X1
       grind)
    | exact resolve eq12 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq2915 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2860 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq3922 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq2915 X1 (σ X0) X2
       grind)
    | exact superpose eq2915 eq42
    | (have j1 := eq2915 X1 X1 X2
       grind)
    | exact resolve eq42 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2915
  have eq3968 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3922 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3922
    | (have j0 := eq3922 X0 X1 X2
       grind)
    | exact resolve eq3922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq12312 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (τ (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3968 X2 (σ X1) (σ X0)
       grind)
    | exact superpose eq3968 eq15
    | (have j1 := eq3968 X2 (σ X1) X2
       grind)
    | exact resolve eq15 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq12328 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12312 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq12312
    | (have j0 := eq12312 X0 X1 X2
       grind)
    | exact resolve eq12312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12312
  have eq15220 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq78413 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2838 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2838
    | (have j0 := eq2838 X0 X1
       grind)
    | exact resolve eq2838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq79043 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78413 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq78413
    | (have j0 := eq78413 X0 X1
       grind)
    | exact resolve eq78413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78413
  have eq80880 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq79043 X2 X0
       grind)
    | exact superpose eq79043 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq79043 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq79043 X0 X1
       grind)
    | exact resolve eq12 eq79043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79043
  have eq81282 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80880 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80880
  have eq120543 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15220 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15220
    | (have j0 := eq15220 (τ X0)
       grind)
    | exact resolve eq15220 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq120627 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq120543 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120543
    | (have j0 := eq120543 X0
       grind)
    | exact resolve eq120543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120543
  have eq120660 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq120627 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120627
    | (have j0 := eq120627 X0
       grind)
    | exact resolve eq120627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120627
  have eq188469 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq12328 x y X0
       grind)
    | exact superpose eq12328 eq16
    | (have j1 := eq12328 X0 y X0
       grind)
    | exact resolve eq16 eq12328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12328
  have eq188810 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq188469 X0
       have j1 := eq81282 y X0 x
       grind)
    | (have r₁ := eq188469 X0
       have r₂ := eq81282 y x x
       grind)
    | exact resolve eq188469 eq81282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81282 eq188469
  have eq192965 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15220 y
       have i₂ := eq188810 y
       grind)
    | exact superpose eq188810 eq15220
    | (have j0 := eq15220 y
       grind)
    | exact resolve eq15220 eq188810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15220
  have eq192967 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq120660 y
       have i₂ := eq188810 y
       grind)
    | exact superpose eq188810 eq120660
    | (have j0 := eq120660 y
       grind)
    | (have r₁ := eq120660 y
       have r₂ := eq188810 y
       grind)
    | exact resolve eq120660 eq188810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120660 eq188810
  have eq193035 : y = (M.op y y) := by grind
  clear eq192967
  have eq193036 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq192965
  have eq195914 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq25 y y x
       have i₂ := eq193035
       grind)
    | exact superpose eq193035 eq25
    | exact resolve eq25 eq193035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196031 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq195914 X0
       have i₂ := eq193035
       grind)
    | exact superpose eq193035 eq195914
    | exact resolve eq195914 eq193035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193035 eq195914
  have eq219675 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ y) (σ y) x
       have i₂ := eq193036
       grind)
    | exact superpose eq193036 eq25
    | exact resolve eq25 eq193036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq219808 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq219675 X0
       have i₂ := eq193036
       grind)
    | exact superpose eq193036 eq219675
    | exact resolve eq219675 eq193036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193036 eq219675
  have eq224611 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq219808 (σ x)
       grind)
    | exact superpose eq219808 eq16
    | exact resolve eq16 eq219808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219808
  have eq224657 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq224611
       have i₂ := eq196031 x
       grind)
    | exact superpose eq196031 eq224611
    | exact resolve eq224611 eq196031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196031 eq224611
  have eq224658 : False := by grind
  exact eq224658

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_x_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq55 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
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
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X2 (M.op X1 X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq14 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq55 x
       have i₂ := eq14 x y X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq234
    | exact resolve eq234 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq257 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq988 : ∀ X1 : G, (M.op (M.op x y) y) ≠ (M.op (M.op y y) (M.op y y)) ∨ (M.op X1 X1) = (k X1 (M.op (M.op y y) (M.op y y))) := by
    intro X1
    first
    | (have i₁ := eq68 x (M.op y y) X1
       have i₂ := eq55 (M.op x (M.op y y))
       grind)
    | exact superpose eq55 eq68
    | (have j0 := eq68 x (M.op y y) X1
       grind)
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op X1 X1) = (k X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X1
    first
    | exact superpose eq56 eq68
    | (have j0 := eq68 x (M.op (σ y) (σ y)) X1
       grind)
    | exact resolve eq68 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq995 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X1
    first
    | (have j0 := eq990 X1
       grind)
    | (have r₁ := eq990 X1
       have r₂ := eq56 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq990 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq997 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op y y) (M.op y y))) := by
    intro X1
    first
    | (have j0 := eq988 X1
       grind)
    | (have r₁ := eq988 X1
       have r₂ := eq55 (M.op y y)
       grind)
    | exact resolve eq988 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1013 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X1
    first
    | exact superpose eq56 eq995
    | exact resolve eq995 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1015 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op x y) y)) := by
    intro X1
    first
    | (have i₁ := eq997 X1
       have i₂ := eq55 (M.op y y)
       grind)
    | exact superpose eq55 eq997
    | exact resolve eq997 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1057 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1015 X0
       have i₂ := eq1013 X0
       grind)
    | exact superpose eq1013 eq1015
    | exact resolve eq1015 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq97 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq97 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1421 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1429 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1421 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1421 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1421 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq11489 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1013 eq1429
    | (have j0 := eq1429 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | exact resolve eq1429 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq11504 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (σ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq235 eq11489
    | (have j0 := eq11489 X0
       grind)
    | exact resolve eq11489 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11489
  have eq11505 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq11504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11504
  have eq11652 : ∀ X0 : G, (k (τ X0) (M.op (M.op (σ x) (σ y)) (σ y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq11505 eq257
    | exact resolve eq257 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq11661 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq11505 eq37
    | exact resolve eq37 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq11663 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq11505 eq36
    | exact resolve eq36 eq11505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq11505
  have eq11686 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq1013 eq11663
    | exact resolve eq11663 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11663
  have eq11688 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1013 eq11661
    | exact resolve eq11661 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq11661
  have eq11697 : ∀ X0 : G, (k (τ X0) (M.op (M.op x y) y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1057 eq11652
    | exact resolve eq11652 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq11652
  have eq11751 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq11686
       grind)
    | exact superpose eq11686 eq16
    | exact resolve eq16 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11817 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq11688 eq16
    | exact resolve eq16 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11688
  have eq12611 : (k (M.op y y) (M.op (M.op x y) y)) = (τ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq11751 eq11697
    | exact resolve eq11697 eq11751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11697
  have eq12718 : (k (M.op y y) (M.op (M.op x y) y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq56 eq12611
    | exact resolve eq12611 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq12611
  have eq12725 : (M.op (M.op y y) (M.op y y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq1015 eq12718
    | exact resolve eq12718 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq12718
  have eq12726 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq12725
       have i₂ := eq55 (M.op y y)
       grind)
    | exact superpose eq55 eq12725
    | exact resolve eq12725 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12725
  have eq12727 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq12726 eq15
    | exact resolve eq15 eq12726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq29882
    | exact resolve eq29882 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29882
  have eq29894 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq29883
       have r₂ := eq27
       grind)
    | exact resolve eq29883 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29883
  have eq29896 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq29894
    | exact resolve eq29894 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29894
  have eq29899 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29896 eq11751
    | exact resolve eq11751 eq29896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29896
  have eq29998 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq29899
    | exact resolve eq29899 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899
  have eq29999 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq29998
  have eq30026 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq29999
       grind)
    | exact superpose eq29999 eq57
    | exact resolve eq57 eq29999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30650 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30026 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30026
    | (have j0 := eq30026 x X0
       grind)
    | exact resolve eq30026 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026
  have eq31278 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29999
       have i₂ := eq30650 y
       grind)
    | exact superpose eq30650 eq29999
    | exact resolve eq29999 eq30650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29999 eq30650
  have eq31302 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31278
  have eq31442 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31302 eq81
    | (have r₁ := eq81
       have r₂ := eq31302
       grind)
    | exact resolve eq81 eq31302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq31302
  have eq31458 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31442
  have eq37033 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31458 eq11751
    | exact resolve eq11751 eq31458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751 eq31458
  have eq37146 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq37033
    | exact resolve eq37033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37033
  have eq39382 : (τ (σ x)) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37146 eq62
    | exact resolve eq62 eq37146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq39383 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37146 eq119
    | exact resolve eq119 eq37146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq37146
  have eq39391 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39383
  have eq39400 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq39382
    | exact resolve eq39382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39382
  have eq39407 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq39400
       have r₂ := eq80
       grind)
    | exact resolve eq39400 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq39400
  have eq39432 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq39407
       grind)
    | exact superpose eq39407 eq57
    | exact resolve eq57 eq39407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40645 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 y x
       have i₂ := eq39391
       grind)
    | exact superpose eq39391 eq57
    | exact resolve eq57 eq39391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq41484 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq39407
       have i₂ := eq39432 y X0
       grind)
    | (have i₁ := eq39407
       have i₂ := eq39432 X0 y
       grind)
    | exact superpose eq39432 eq39407
    | exact resolve eq39407 eq39432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39407 eq39432
  have eq41511 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq41484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41484
  have eq43139 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12727
       have i₂ := eq41511 sF0
       grind)
    | exact superpose eq41511 eq12727
    | exact resolve eq12727 eq41511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41511
  have eq43180 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq43139
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43139
    | exact resolve eq43139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43139
  have eq44917 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq43180 eq235
    | exact resolve eq235 eq43180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43180
  have eq45314 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44917
    | (have j0 := eq44917 (σ x)
       grind)
    | exact resolve eq44917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44917
  have eq45629 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq45314
       grind)
    | exact superpose eq45314 eq44
    | exact resolve eq44 eq45314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq45314
  have eq45644 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45629
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45629
    | exact resolve eq45629 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45629
  have eq45664 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45644 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq45644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45644
  have eq45665 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq45664
    | exact resolve eq45664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45664
  have eq45676 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq45665
    | exact resolve eq45665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45665
  have eq45677 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45676
  have eq80200 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq40645 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40645
    | (have j0 := eq40645 x X0
       grind)
    | exact resolve eq40645 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40645
  have eq82119 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39391
       have i₂ := eq80200 y
       grind)
    | exact superpose eq80200 eq39391
    | exact resolve eq39391 eq80200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39391 eq80200
  have eq82167 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq82119
  have eq82428 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq82167 eq28
    | exact resolve eq28 eq82167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82167
  have eq82574 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq82428
    | exact resolve eq82428 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82428
  have eq82596 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82574 eq20
    | exact resolve eq20 eq82574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82665 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82574 eq12727
    | exact resolve eq12727 eq82574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82574
  have eq82701 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82665
       have i₂ := eq11686
       grind)
    | exact superpose eq11686 eq82665
    | exact resolve eq82665 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11686 eq82665
  have eq82765 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82596
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq82596
    | exact resolve eq82596 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq82596
  have eq82811 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82765 eq26
    | exact resolve eq26 eq82765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82890 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82765 eq12726
    | exact resolve eq12726 eq82765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82923 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82765 eq45677
    | exact resolve eq45677 eq82765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45677
  have eq82942 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq82923
       have r₂ := eq27
       grind)
    | exact resolve eq82923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82923
  have eq86964 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82765 eq82701
    | exact resolve eq82701 eq82765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82701 eq82765
  have eq87021 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq86964
  have eq98934 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87021 eq82890
    | exact resolve eq82890 eq87021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98936 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82890 eq15
    | exact resolve eq15 eq82890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82890
  have eq98966 : (M.op (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq98934
  have eq98975 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12727 eq98936
    | exact resolve eq98936 eq12727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98936
  have eq98976 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11817 eq98966
    | exact resolve eq98966 eq11817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98966
  have eq102014 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82942 eq11817
    | exact resolve eq11817 eq82942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82942
  have eq102153 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq102014
    | exact resolve eq102014 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq102014
  have eq102168 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102153 eq98976
    | exact resolve eq98976 eq102153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102153
  have eq102272 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq102168
  have eq102325 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102272 eq12727
    | exact resolve eq12727 eq102272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102272
  have eq102437 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq102325
    | exact resolve eq102325 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102325
  have eq103228 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq102437 eq235
    | exact resolve eq235 eq102437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq102437
  have eq107428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103228 eq82811
    | exact resolve eq82811 eq103228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82811 eq103228
  have eq107435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107428
  have eq107446 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107435
       have r₂ := eq27
       grind)
    | exact resolve eq107435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107435
  have eq107496 : (M.op (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107446 eq12726
    | exact resolve eq12726 eq107446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq107510 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107446 eq87021
    | exact resolve eq87021 eq107446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87021
  have eq107517 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq107510
  have eq107529 : (M.op (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq107496
    | exact resolve eq107496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107496
  have eq109880 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107529 eq12727
    | exact resolve eq12727 eq107529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107529
  have eq110001 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109880
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq109880
    | exact resolve eq109880 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109880
  have eq110064 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110001 eq98975
    | exact resolve eq98975 eq110001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98975 eq110001
  have eq110105 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq110064
  have eq110166 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107446 eq110105
    | exact resolve eq110105 eq107446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107446 eq110105
  have eq110217 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq110166
  have eq117788 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107517 eq110217
    | exact resolve eq110217 eq107517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107517 eq110217
  have eq117828 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq117788
  have eq117837 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117828 eq11817
    | exact resolve eq11817 eq117828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11817 eq117828
  have eq118006 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq117837
    | exact resolve eq117837 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq117837
  have eq118030 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118006 eq98976
    | exact resolve eq98976 eq118006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98976 eq118006
  have eq118162 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq118030
  have eq118320 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118162 eq213
    | exact resolve eq213 eq118162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq118162
  have eq118417 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118320
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118320
    | exact resolve eq118320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118320
  have eq118418 : x = (M.op x y) := by grind
  clear eq118417
  have eq118476 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq118418 eq20
    | exact resolve eq20 eq118418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118545 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq118418 eq12727
    | exact resolve eq12727 eq118418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12727 eq118418
  have eq118631 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq118545
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118545
    | exact resolve eq118545 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq118545
  have eq118699 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq118476
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118476
    | exact resolve eq118476 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118476
  have eq118736 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20 eq118631
    | exact resolve eq118631 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq118631
  have eq118790 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq118699 eq26
    | exact resolve eq26 eq118699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq118699
  have eq118987 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq118736 eq227
    | exact resolve eq227 eq118736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq118736
  have eq122960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq118790 eq118987
    | exact resolve eq118987 eq118790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118790 eq118987
  have eq122961 : False := by grind
  exact eq122961

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation450 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq171 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1041 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq170 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq170
    | exact resolve eq170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1111 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1041 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1041
    | (have j0 := eq1041 X0 X1
       grind)
    | exact resolve eq1041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq2841 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq16
    | (have j1 := eq171 x y
       grind)
    | exact resolve eq16 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq171 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq16533 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2841
       have i₂ := eq1111 x y
       grind)
    | exact superpose eq1111 eq2841
    | (have j1 := eq1111 (σ x) (σ y)
       grind)
    | (have r₁ := eq2841
       have r₂ := eq1111 x y
       grind)
    | (have r₁ := eq2841
       have r₂ := eq1111 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2841
       have r₂ := eq1111 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2841 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2841
  have eq16534 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16533
  have eq21291 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16534
       grind)
    | exact superpose eq16534 eq16
    | exact resolve eq16 eq16534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16534
  have eq21292 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21291
       have r₂ := eq22 x
       grind)
    | exact resolve eq21291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21294 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq21292
       grind)
    | exact superpose eq21292 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21292
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21292
       grind)
    | exact resolve eq13 eq21292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 y x
       have i₂ := eq21292
       grind)
    | exact superpose eq21292 eq110
    | exact resolve eq110 eq21292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21292
  have eq21312 : (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21294
  have eq21319 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110 (σ y) (σ x)
       have i₂ := eq21297
       grind)
    | exact superpose eq21297 eq110
    | exact resolve eq110 eq21297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq21297
  have eq21345 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21319
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq21319
    | exact resolve eq21319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21319
  have eq21360 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21345
       grind)
    | exact superpose eq21345 eq10
    | exact resolve eq10 eq21345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21345
  have eq21422 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21360
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21360
    | exact resolve eq21360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21360
  have eq21424 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21422
       grind)
    | exact superpose eq21422 eq16
    | exact resolve eq16 eq21422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21422
  have eq21425 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq21424
       have r₂ := eq22 x
       grind)
    | exact resolve eq21424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21424
  have eq21831 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq21425
       grind)
    | exact superpose eq21425 eq10
    | exact resolve eq10 eq21425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21425
  have eq21894 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21831
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21831
    | exact resolve eq21831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21831
  have eq21895 : y = (M.op y y) := by grind
  clear eq21894
  have eq404419 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2852 x y
       have i₂ := eq21312
       grind)
    | exact superpose eq21312 eq2852
    | (have j0 := eq2852 x y
       grind)
    | exact resolve eq2852 eq21312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852 eq21312
  have eq404479 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq404419
  have eq404557 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq404479
       have i₂ := eq21895
       grind)
    | exact superpose eq21895 eq404479
    | exact resolve eq404479 eq21895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404479
  have eq404558 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq404557
  have eq404606 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq404558
       grind)
    | exact superpose eq404558 eq10
    | exact resolve eq10 eq404558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404558
  have eq404784 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq404606
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq404606
    | exact resolve eq404606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404606
  have eq404785 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq404784
  have eq404798 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq404785
       grind)
    | exact superpose eq404785 eq16
    | exact resolve eq16 eq404785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404831 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq404785
       grind)
    | exact superpose eq404785 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq404785
       grind)
    | exact resolve eq13 eq404785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404785
  have eq404938 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq404831
  have eq405015 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq404938
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq404938
    | exact resolve eq404938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404938
  have eq405082 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq405015
       have i₂ := eq21895
       grind)
    | exact superpose eq21895 eq405015
    | exact resolve eq405015 eq21895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21895 eq405015
  have eq405118 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq405082
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq405082
    | exact resolve eq405082 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405082
  have eq405152 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1111 x y
       have i₂ := eq405118
       grind)
    | exact superpose eq405118 eq1111
    | (have j0 := eq1111 x y
       grind)
    | exact resolve eq1111 eq405118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq405118
  have eq405297 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq405152
  have eq405339 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq405297
       have r₂ := eq404798
       grind)
    | exact resolve eq405297 eq404798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405297
  have eq405604 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq405339
       grind)
    | exact superpose eq405339 eq10
    | exact resolve eq10 eq405339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405339
  have eq405783 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq405604
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq405604
    | exact resolve eq405604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405604
  have eq405784 : y = (M.op x y) ∨ x = y := by grind
  clear eq405783
  have eq405799 : (σ y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq404798
       have i₂ := eq405784
       grind)
    | exact superpose eq405784 eq404798
    | exact resolve eq404798 eq405784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404798 eq405784
  have eq405991 : (σ y) ≠ (σ y) ∨ x = y := by grind
  clear eq405799
  have eq405992 : x = y := by grind
  clear eq405991
  have eq407009 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq405992
       grind)
    | exact superpose eq405992 eq16
    | exact resolve eq16 eq405992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405992
  have eq407412 : False := by grind
  exact eq407412

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pxx_pyx_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  clear eq44
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq10
    | exact resolve eq10 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq50
    | exact resolve eq50 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq87 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq86
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq86
    | exact resolve eq86 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq82 sF3
       grind)
    | exact superpose eq82 eq80
    | exact resolve eq80 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq96
    | exact resolve eq96 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq105 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op x y) := by
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
  have eq108 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq63
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq108
    | exact resolve eq108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq123 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X2 X3
       have i₂ := eq56 (M.op X0 X0) X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1 x x
       have i₂ := eq56 (M.op x x) X0
       grind)
    | exact superpose eq56 eq241
    | exact resolve eq241 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq328 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq82 (τ X0)
       grind)
    | exact superpose eq82 eq35
    | exact resolve eq35 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq339 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq328
    | exact resolve eq328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq341 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq339
    | exact resolve eq339 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq339
  have eq523 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq89 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq89
    | exact resolve eq89 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq523
       have i₂ := eq56 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq56 eq523
    | exact resolve eq523 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq560 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq556
       have i₂ := eq56 (M.op y y) y
       grind)
    | exact superpose eq56 eq556
    | exact resolve eq556 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq801 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq89 (M.op (τ X0) (τ X0))
       have i₂ := eq341 X0
       grind)
    | exact superpose eq341 eq89
    | exact resolve eq89 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq341
  have eq803 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op x y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq801 X0
       have i₂ := eq56 (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq56 eq801
    | exact resolve eq801 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq811 : ∀ X0 : G, (M.op (M.op x y) X0) = (σ (M.op (M.op x y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq803 X0
       have i₂ := eq56 (M.op X0 X0) X0
       grind)
    | exact superpose eq56 eq803
    | exact resolve eq803 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq843 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq811 eq16
    | exact resolve eq16 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq958 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (M.op X1 (τ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq843 eq247
    | exact resolve eq247 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1377 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (σ (k X0 X1)) X3) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (σ X1) (σ X0)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq14
    | (have j1 := eq98 X0 X1
       grind)
    | exact resolve eq14 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1379 : ∀ X0 X1 X3 : G, (M.op (M.op x y) X3) = (M.op (σ (k X0 X1)) X3) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1377 X0 X1 x X3
       have i₂ := eq56 x X3
       grind)
    | exact superpose eq56 eq1377
    | (have j0 := eq1377 X0 X1 x X3
       grind)
    | exact resolve eq1377 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1377
  have eq5799 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq329
    | exact resolve eq329 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq5889 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5799 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5799
    | (have j0 := eq5799 X0 X1
       grind)
    | exact resolve eq5799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq6549 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (M.op (σ (M.op X0 X1)) X2) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1379 X1 X0 X2
       have i₂ := eq11 X1 X0
       grind)
    | exact superpose eq11 eq1379
    | (have j0 := eq1379 X0 X1 x
       have j1 := eq11 (M.op (M.op x y) X2) (M.op (σ (M.op X0 X1)) X2)
       grind)
    | exact resolve eq1379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq10703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq10703
    | exact resolve eq10703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10703
  have eq10712 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq10704
       have r₂ := eq28
       grind)
    | exact resolve eq10704 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10704
  have eq10715 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq10712 eq238
    | exact resolve eq238 eq10712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10716 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq10712 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10712
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10712
       grind)
    | exact resolve eq13 eq10712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10718 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq10716
  have eq10720 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq10715
    | (have j0 := eq10715 (σ y)
       grind)
    | exact resolve eq10715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10897 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq10720 eq958
    | exact resolve eq958 eq10720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq10720
  have eq11296 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq10718 eq112
    | exact resolve eq112 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq10718
  have eq11304 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq11296
  have eq11518 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11304 eq10715
    | exact resolve eq10715 eq11304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10715 eq11304
  have eq11532 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq11518
  have eq11702 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq11532 eq247
    | exact resolve eq247 eq11532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11532
  have eq18849 : (τ (k (σ x) (σ y))) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq18904 : (k x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq63 eq18849
    | exact resolve eq18849 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18849
  have eq916456 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq10712 eq109
    | exact resolve eq109 eq10712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq10712
  have eq916966 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq916456
  have eq916980 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq916966
    | exact resolve eq916966 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916966
  have eq917002 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18904
       have i₂ := eq916980
       grind)
    | exact superpose eq916980 eq18904
    | exact resolve eq18904 eq916980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18904 eq916980
  have eq917032 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq917002
  have eq917142 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq238 y x X0
       have i₂ := eq917032
       grind)
    | exact superpose eq917032 eq238
    | exact resolve eq238 eq917032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917144 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6549 y x X0
       have i₂ := eq917032
       grind)
    | exact superpose eq917032 eq6549
    | (have j0 := eq6549 y x x
       grind)
    | exact resolve eq6549 eq917032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549 eq917032
  have eq917148 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq917144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917144
  have eq917152 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917148 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq917148
    | (have j0 := eq917148 X0
       grind)
    | exact resolve eq917148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917148
  have eq917157 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917152 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq917152
    | (have j0 := eq917152 X0
       grind)
    | exact resolve eq917152 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917152
  have eq917158 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917157 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq917157
    | (have j0 := eq917157 X0
       grind)
    | exact resolve eq917157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917157
  have eq917159 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq917158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917158
  have eq917160 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq917159 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq917159
    | (have j0 := eq917159 X0
       grind)
    | exact resolve eq917159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917159
  have eq917161 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq917160 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq917160
    | (have j0 := eq917160 X0
       grind)
    | exact resolve eq917160 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917160
  have eq917162 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq917161
    | (have j0 := eq917161 X0
       grind)
    | exact resolve eq917161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917161
  have eq917163 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq917162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917162
  have eq917164 : ∀ X0 : G, y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq917163 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq917163
    | (have j0 := eq917163 X0
       grind)
    | exact resolve eq917163 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917163
  have eq917165 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq917164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917164
  have eq918243 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq917142 eq560
    | exact resolve eq560 eq917142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917142
  have eq919039 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq918243
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq918243
    | exact resolve eq918243 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918243
  have eq919071 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq919039
    | exact resolve eq919039 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919039
  have eq925183 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq917165
    | (have j0 := eq917165 (σ y)
       grind)
    | exact resolve eq917165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917165
  have eq925999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq925183 eq919071
    | exact resolve eq919071 eq925183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919071 eq925183
  have eq926031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq925999
  have eq926035 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq926031
       have r₂ := eq28
       grind)
    | exact resolve eq926031 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926031
  have eq926038 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq926035 eq72
    | (have r₁ := eq72
       have r₂ := eq926035
       grind)
    | exact resolve eq72 eq926035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq926044 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq926035 eq10897
    | exact resolve eq10897 eq926035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897 eq926035
  have eq926597 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq926044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926044
  have eq926600 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq926038
  have eq926654 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq926597
    | exact resolve eq926597 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926597
  have eq927415 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq926600 eq63
    | exact resolve eq63 eq926600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq926600
  have eq927472 : (k x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq123 eq927415
    | exact resolve eq927415 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq927415
  have eq927479 : (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq927472
       have r₂ := eq71
       grind)
    | exact resolve eq927472 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq927472
  have eq927516 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5889 x y
       have i₂ := eq927479
       grind)
    | exact superpose eq927479 eq5889
    | (have j0 := eq5889 x y
       grind)
    | exact resolve eq5889 eq927479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889 eq927479
  have eq927526 : (σ (M.op y y)) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq927516
  have eq927545 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq927526
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq927526
    | exact resolve eq927526 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq927526
  have eq927573 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq927545
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq927545
    | exact resolve eq927545 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927545
  have eq954695 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq926654 x
       grind)
    | exact superpose eq926654 eq19
    | (have j1 := eq926654 x
       grind)
    | exact resolve eq19 eq926654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926654
  have eq954787 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq954695
  have eq955054 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq927573
       have i₂ := eq954787
       grind)
    | exact superpose eq954787 eq927573
    | exact resolve eq927573 eq954787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927573
  have eq955068 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq238 y x X0
       have i₂ := eq954787
       grind)
    | exact superpose eq954787 eq238
    | exact resolve eq238 eq954787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954787
  have eq955087 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq955054
  have eq955096 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq955087
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq955087
    | exact resolve eq955087 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955087
  have eq955270 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq955096 eq238
    | exact resolve eq238 eq955096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955096
  have eq964854 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq955068 eq560
    | exact resolve eq560 eq955068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955068
  have eq965728 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq964854
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq964854
    | exact resolve eq964854 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964854
  have eq965762 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq965728
    | exact resolve eq965728 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965728
  have eq1337579 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq955270
    | (have j0 := eq955270 (σ y)
       grind)
    | exact resolve eq955270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955270
  have eq1338459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1337579 eq965762
    | exact resolve eq965762 eq1337579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965762 eq1337579
  have eq1338512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1338459
  have eq1338538 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1338512
       have r₂ := eq28
       grind)
    | exact resolve eq1338512 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338512
  have eq1338547 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1338538 eq30
    | exact resolve eq30 eq1338538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338538
  have eq1339010 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1338547
    | exact resolve eq1338547 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338547
  have eq1339011 : y = (M.op x y) ∨ x = y := by grind
  clear eq1339010
  have eq1339056 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1339011 eq21
    | exact resolve eq21 eq1339011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339011
  have eq1341468 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1339056
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1339056
    | exact resolve eq1339056 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339056
  have eq1341636 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1341468 eq27
    | exact resolve eq27 eq1341468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341468
  have eq1342752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1341636 eq11702
    | exact resolve eq11702 eq1341636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq1342811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1342752
  have eq1342829 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1342811
       have r₂ := eq28
       grind)
    | exact resolve eq1342811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342811
  have eq1366155 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq238 y x X0
       have i₂ := eq1342829
       grind)
    | exact superpose eq1342829 eq238
    | exact resolve eq238 eq1342829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1342829
  have eq1590500 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1366155 eq560
    | exact resolve eq560 eq1366155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq1366155
  have eq1591756 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1590500
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1590500
    | exact resolve eq1590500 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590500
  have eq1591814 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq1591756
    | exact resolve eq1591756 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591756
  have eq1592265 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1591814 eq247
    | exact resolve eq247 eq1591814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq1591814
  have eq1597076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1592265 eq1341636
    | exact resolve eq1341636 eq1592265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341636 eq1592265
  have eq1597090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1597076
  have eq1597284 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1597090
       have r₂ := eq28
       grind)
    | exact resolve eq1597090 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597090
  have eq1597357 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1597284 eq30
    | exact resolve eq30 eq1597284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1597284
  have eq1598263 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1597357
    | exact resolve eq1597357 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1597357
  have eq1598264 : x = y := by grind
  clear eq1598263
  have eq1598384 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1598264
       grind)
    | exact superpose eq1598264 eq19
    | exact resolve eq19 eq1598264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1598385 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1598264
       grind)
    | exact superpose eq1598264 eq25
    | exact resolve eq25 eq1598264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1598264
  have eq1599382 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1598385
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1598385
    | exact resolve eq1598385 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1598385
  have eq1599568 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1599382 eq27
    | exact resolve eq27 eq1599382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1599382
  have eq1600802 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1599568 eq87
    | exact resolve eq87 eq1599568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1599568
  have eq1600962 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1600802
       have i₂ := eq1598384
       grind)
    | exact superpose eq1598384 eq1600802
    | exact resolve eq1600802 eq1598384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598384 eq1600802
  have eq1601056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1600962 eq15
    | exact resolve eq15 eq1600962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600962
  have eq1601750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1601056
    | exact resolve eq1601056 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1601056
  have eq1601911 : False := by grind
  exact eq1601911

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pyy_pyx_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) (k X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X1 X1)
       have r₂ := eq13 X0 X1
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 x X2 X4 X5
       have i₂ := eq16 x X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
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
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X2 X2) x x
       have i₂ := eq16 (M.op x x) X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (k (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X0 X1 X2 X3
       have i₂ := eq175 (M.op X2 X2)
       grind)
    | exact superpose eq175 eq184
    | exact resolve eq184 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq182
    | exact resolve eq182 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq188 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq181
    | exact resolve eq181 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq191 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (k (k X2 X2) (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq185 X0 X1 X0 X3
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq185
    | exact resolve eq185 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq194 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ x) (σ y)) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 X0 X1 X2 x
       have i₂ := eq187 x (k X2 X2)
       grind)
    | exact superpose eq187 eq191
    | exact resolve eq191 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq195 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194 X0 X1 X1
       have i₂ := eq187 sF4 X1
       grind)
    | exact superpose eq187 eq194
    | exact resolve eq194 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq196 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X2 X2) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X2 X2)
       have i₂ := eq16 (M.op X2 X2) X2 X0 X1
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X2) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 X0 X1 X2
       have i₂ := eq175 X2
       grind)
    | exact superpose eq175 eq199
    | exact resolve eq199 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (k X2 X2) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 X0 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq196
    | exact resolve eq196 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq206 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq202 X0 x X2
       have i₂ := eq187 x X2
       grind)
    | exact superpose eq187 eq202
    | exact resolve eq202 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq208 : ∀ X2 : G, (k (k X2 X2) (k X2 X2)) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X2
    first
    | (have i₁ := eq205 x x X2
       have i₂ := eq195 x x X2
       grind)
    | (have i₁ := eq205 (σ x) (σ y) X2
       have i₂ := eq195 x x X2
       grind)
    | exact superpose eq195 eq205
    | (have j0 := eq205 (σ x) (σ y) X2
       grind)
    | exact resolve eq205 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq210 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq187
    | exact resolve eq187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq187 x X0
       have i₂ := eq188 x X0
       grind)
    | exact superpose eq188 eq187
    | exact resolve eq187 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq175 (k X0 X0)
       have i₂ := eq188 (k X0 X0) X0
       grind)
    | exact superpose eq188 eq175
    | exact resolve eq175 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (k X0 X0)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (k X0 X0) X2 X3
       have i₂ := eq188 (k X0 X0) X0
       grind)
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1 x x
       have i₂ := eq187 (M.op x x) X0
       grind)
    | exact superpose eq187 eq228
    | exact resolve eq228 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq228
  have eq235 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq226 eq232
    | exact resolve eq232 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq241 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq226 eq175
    | exact resolve eq175 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq206
    | exact resolve eq206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq294 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq226 eq279
    | exact resolve eq279 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq480 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq537 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq564 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq480
    | exact resolve eq480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq659 : ∀ X0 : G, (k (σ (k X0 X0)) (σ (k X0 X0))) = (M.op (M.op x y) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq175 (σ (k X0 X0))
       have i₂ := eq294 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq294 eq175
    | exact resolve eq175 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq659 X0
       have i₂ := eq210 X0 sF0
       grind)
    | exact superpose eq210 eq659
    | exact resolve eq659 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq659
  have eq680 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq669 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq669
    | exact resolve eq669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq685 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq680 X0
       have i₂ := eq208 X0
       grind)
    | exact superpose eq208 eq680
    | exact resolve eq680 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq680
  have eq687 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq226 eq685
    | exact resolve eq685 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq689 : ∀ X0 : G, (M.op (M.op x y) (σ X0)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq226 eq687
    | exact resolve eq687 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq716 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq689 sF0
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq689
    | exact resolve eq689 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (M.op (M.op x y) (σ X0))) := by
    intro X0
    first
    | exact superpose eq689 eq15
    | exact resolve eq15 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq716
    | exact resolve eq716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq743 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq738
    | exact resolve eq738 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq746 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq743
    | exact resolve eq743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq789 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq721 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq721
    | exact resolve eq721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) (σ x))) := by
    first
    | (have i₁ := eq721 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq721
    | (have j0 := eq721 x
       grind)
    | exact resolve eq721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq859 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq235 eq13
    | (have j0 := eq13 X1 (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op x y) X0)
       have r₂ := eq235 X0 X1
       grind)
    | exact resolve eq13 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq875 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq870
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq870
    | exact resolve eq870 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq878 : y ≠ (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq867
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq867
    | exact resolve eq867 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq886 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X1 X1
       have i₂ := eq195 sF0 X1 (M.op sF0 X1)
       grind)
    | exact superpose eq195 eq872
    | exact resolve eq872 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq895 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq226 eq886
    | exact resolve eq886 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq901 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq235 eq895
    | exact resolve eq895 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq930 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (k X0 X1) X2) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq195
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq942 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) := by
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
  have eq950 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq970 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (M.op (k X0 X1) X2) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq226 eq930
    | (have j0 := eq930 X0 X1 X2
       grind)
    | exact resolve eq930 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq930
  have eq1026 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (k X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq901 sF0 x
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq901
    | exact resolve eq901 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (k X1 (τ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq901 eq537
    | exact resolve eq537 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq901
  have eq1131 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (M.op X1 (τ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq789 eq235
    | exact resolve eq235 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq1254 : ∀ X0 X1 : G, (M.op (M.op x y) (τ X0)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X1 (τ X0)
       have i₂ := eq564 X0 X0
       grind)
    | exact superpose eq564 eq188
    | exact resolve eq188 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq1257 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq789 eq1254
    | exact resolve eq1254 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq1254
  have eq1434 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 X1 X2 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2722 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq40
    | exact resolve eq40 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq2723 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2722
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2722
    | exact resolve eq2722 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq2725 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq2723
    | exact resolve eq2723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq3622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2725 eq950
    | exact resolve eq950 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq3629 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq3622
       have r₂ := eq27
       grind)
    | exact resolve eq3622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq3637 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq3629 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3638 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq3629 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3629
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3629
       grind)
    | exact resolve eq13 eq3629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3645 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3629 eq1434
    | exact resolve eq1434 eq3629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq3646 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq3638
  have eq3647 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq3637
  have eq3655 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq3646
       have r₂ := eq28 (k (σ y) (σ x)) (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq3646
       have r₂ := eq28 (M.op (σ x) (σ x)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq3646
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq3646 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3656 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq3647
    | exact resolve eq3647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq3662 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3655
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq3655
    | exact resolve eq3655 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655
  have eq3664 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2725 eq3662
    | exact resolve eq3662 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725 eq3662
  have eq3675 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq3664 eq227
    | exact resolve eq227 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3680 : ∀ X0 : G, (τ (M.op (M.op x y) (σ x))) = (M.op X0 (τ (σ (M.op x y)))) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3664 eq1257
    | exact resolve eq1257 eq3664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq3664
  have eq3686 : ∀ X0 : G, (τ (M.op (M.op x y) (σ x))) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq29 eq3680
    | exact resolve eq3680 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3680
  have eq3695 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq799 eq3686
    | exact resolve eq3686 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq3686
  have eq4243 : ∀ X0 : G, (M.op (M.op x y) (σ x)) = (σ (M.op X0 (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3695 eq689
    | exact resolve eq689 eq3695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq4300 : ∀ X0 : G, (M.op (M.op x y) (σ x)) = (σ (M.op X0 (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4243 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4243
    | (have j0 := eq4243 X0
       grind)
    | exact resolve eq4243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4303 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3675 eq4300
    | exact resolve eq4300 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675 eq4300
  have eq5857 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq3645 eq26
    | (have j1 := eq3645 (σ y)
       grind)
    | exact resolve eq26 eq3645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq5938 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq5857 eq1131
    | exact resolve eq1131 eq5857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq8726 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq3656 eq153
    | exact resolve eq153 eq3656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3656
  have eq8731 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq8726
    | exact resolve eq8726 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8726
  have eq25261 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq970 x y X0
       have i₂ := eq8731
       grind)
    | exact superpose eq8731 eq970
    | (have j0 := eq970 x y x
       grind)
    | exact resolve eq970 eq8731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8731
  have eq25469 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq25261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25261
  have eq25472 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq25469 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25469
    | (have j0 := eq25469 X0
       grind)
    | exact resolve eq25469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq53103 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25472 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq25472 x
       grind)
    | exact superpose eq25472 eq18
    | (have j1 := eq25472 y
       grind)
    | exact resolve eq18 eq25472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25472
  have eq53450 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq53103 eq689
    | exact resolve eq689 eq53103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53103
  have eq53501 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53450
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53450
    | exact resolve eq53450 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53450
  have eq53502 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq53501
    | exact resolve eq53501 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53501
  have eq53618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq53502 eq5857
    | exact resolve eq5857 eq53502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857 eq53502
  have eq53664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53618
  have eq53683 : x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53664
       have r₂ := eq27
       grind)
    | exact resolve eq53664 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53664
  have eq53690 : x = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq53683
       grind)
    | exact superpose eq53683 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq53683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53699 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1434 y x X0
       have i₂ := eq53683
       grind)
    | exact superpose eq53683 eq1434
    | exact resolve eq1434 eq53683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53683
  have eq53701 : x = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53690
  have eq53710 : y = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53701
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53701
    | exact resolve eq53701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53701
  have eq53711 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53710
  have eq53768 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq53711
       grind)
    | exact superpose eq53711 eq41
    | exact resolve eq41 eq53711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53711
  have eq53776 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53768
    | exact resolve eq53768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53768
  have eq53787 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53776 eq970
    | (have j0 := eq970 (σ x) (σ y) x
       grind)
    | exact resolve eq970 eq53776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq53776
  have eq53790 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq53787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53787
  have eq53792 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq53790
    | (have j0 := eq53790 X0
       grind)
    | exact resolve eq53790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53790
  have eq53793 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq53792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53792
  have eq53864 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq53699 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq53699 x
       grind)
    | exact superpose eq53699 eq18
    | (have j1 := eq53699 y
       grind)
    | exact resolve eq18 eq53699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53699
  have eq54206 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53864 eq689
    | exact resolve eq689 eq53864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq53864
  have eq54258 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54206
    | exact resolve eq54206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54206
  have eq54259 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54258
    | exact resolve eq54258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54258
  have eq56093 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53793 eq26
    | (have j1 := eq53793 (σ y)
       grind)
    | exact resolve eq26 eq53793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53793
  have eq56431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq54259 eq56093
    | exact resolve eq56093 eq54259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54259 eq56093
  have eq56436 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq56431
       have r₂ := eq27
       grind)
    | exact resolve eq56431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56431
  have eq56658 : (k (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56436 eq241
    | exact resolve eq241 eq56436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq56660 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56436 eq875
    | (have r₁ := eq875
       have r₂ := eq56436
       grind)
    | exact resolve eq875 eq56436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq56673 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq56436 eq5938
    | exact resolve eq5938 eq56436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938
  have eq56818 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56673
  have eq56825 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq56660
  have eq56849 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq56818
    | exact resolve eq56818 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56818
  have eq56859 : (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56825 eq56658
    | exact resolve eq56658 eq56825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56658
  have eq57291 : (k y y) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56825 eq116
    | exact resolve eq116 eq56825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq56825
  have eq57329 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq99 eq57291
    | exact resolve eq57291 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57291
  have eq57339 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57329
       have r₂ := eq878
       grind)
    | exact resolve eq57329 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq57329
  have eq57348 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq57339
       grind)
    | exact superpose eq57339 eq41
    | exact resolve eq41 eq57339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57356 : (M.op (M.op x y) y) = (k (k x y) (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq227 y
       have i₂ := eq57339
       grind)
    | exact superpose eq57339 eq227
    | exact resolve eq227 eq57339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57339
  have eq57375 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57348
    | exact resolve eq57348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57348
  have eq57382 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57375
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq57375
    | exact resolve eq57375 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57375
  have eq57386 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57382
    | exact resolve eq57382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57382
  have eq57400 : (M.op (M.op x y) (σ y)) = (k (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq57386 eq227
    | exact resolve eq227 eq57386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq57386
  have eq58961 : ∀ X0 : G, (τ (k (σ x) (σ y))) = (k X0 (τ (k (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq56859 eq1038
    | exact resolve eq1038 eq56859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq56859
  have eq59028 : ∀ X0 : G, (k x y) = (k X0 (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq99 eq58961
    | exact resolve eq58961 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq58961
  have eq68496 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56849 x
       grind)
    | exact superpose eq56849 eq18
    | (have j1 := eq56849 x
       grind)
    | exact resolve eq18 eq56849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56849
  have eq68568 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq68496
  have eq68707 : x = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq68568
       grind)
    | exact superpose eq68568 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq68568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68716 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1434 y x X0
       have i₂ := eq68568
       grind)
    | exact superpose eq68568 eq1434
    | exact resolve eq1434 eq68568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68568
  have eq68718 : x = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq68707
  have eq68727 : y = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68718
    | exact resolve eq68718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68718
  have eq68728 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq68727
  have eq69242 : (k x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57356
       have i₂ := eq68728
       grind)
    | exact superpose eq68728 eq57356
    | exact resolve eq57356 eq68728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57356
  have eq69252 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq59028 X0
       have i₂ := eq68728
       grind)
    | exact superpose eq68728 eq59028
    | exact resolve eq59028 eq68728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59028
  have eq69255 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq68728
       grind)
    | exact superpose eq68728 eq41
    | exact resolve eq41 eq68728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq68728
  have eq69263 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq69252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69252
  have eq69273 : (k x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq69242
  have eq69278 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69255
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69255
    | exact resolve eq69255 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69255
  have eq69281 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq69263 eq69273
    | exact resolve eq69273 eq69263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69273
  have eq69319 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq294 x X0
       have i₂ := eq69263 x
       grind)
    | exact superpose eq69263 eq294
    | exact resolve eq294 eq69263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq69353 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq69263 x
       grind)
    | exact superpose eq69263 eq36
    | exact resolve eq36 eq69263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69263
  have eq69415 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq69353
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69353
    | exact resolve eq69353 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69353
  have eq69426 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69319 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69319
    | (have j0 := eq69319 X0
       grind)
    | exact resolve eq69319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69319
  have eq69860 : (k (σ x) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq69278 eq57400
    | exact resolve eq57400 eq69278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57400 eq69278
  have eq69875 : (k (σ x) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq69860
  have eq69887 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq69415 eq69875
    | exact resolve eq69875 eq69415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69415 eq69875
  have eq71108 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq68716 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq68716 x
       grind)
    | exact superpose eq68716 eq18
    | (have j1 := eq68716 y
       grind)
    | exact resolve eq18 eq68716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68716
  have eq71495 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq71108 eq69281
    | exact resolve eq69281 eq71108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281 eq71108
  have eq71542 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq71495
  have eq71568 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq71542 eq32
    | exact resolve eq32 eq71542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71542
  have eq71631 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq71568
    | exact resolve eq71568 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71568
  have eq71632 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq71631
  have eq71636 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq71632
       grind)
    | exact superpose eq71632 eq18
    | exact resolve eq18 eq71632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71632
  have eq72460 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq71636 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq71636
       grind)
    | exact resolve eq13 eq71636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71636
  have eq72468 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq72460
  have eq72519 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have j1 := eq28 x (M.op x y)
       grind)
    | (have r₁ := eq72468
       have r₂ := eq28 (k x (M.op x y)) (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq72468
       have r₂ := eq28 (M.op (M.op x y) (M.op x y)) (k x (M.op x y))
       grind)
    | (have r₁ := eq72468
       have r₂ := eq28 x (M.op x y)
       grind)
    | exact resolve eq72468 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq72468
  have eq72541 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq72519
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq72519
    | exact resolve eq72519 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72519
  have eq72555 : (k (σ x) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq72541 eq36
    | exact resolve eq36 eq72541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72541
  have eq72575 : (k (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq42 eq72555
    | exact resolve eq72555 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq72555
  have eq72578 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq72575
    | exact resolve eq72575 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72575
  have eq72619 : ∀ X0 : G, (M.op (M.op x y) (σ (M.op x y))) = (M.op X0 (k (σ x) (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq72578 eq188
    | exact resolve eq188 eq72578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq72665 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (k (σ x) (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq746 eq72619
    | exact resolve eq72619 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq72619
  have eq72677 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (M.op X0 (k (σ x) (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq72578 eq72665
    | exact resolve eq72665 eq72578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72665
  have eq83336 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq69426 eq26
    | (have j1 := eq69426 (σ y)
       grind)
    | exact resolve eq26 eq69426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69426
  have eq83731 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56436 eq83336
    | exact resolve eq83336 eq56436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56436 eq83336
  have eq83736 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq69887 eq83731
    | exact resolve eq83731 eq69887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69887 eq83731
  have eq83737 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq83736
  have eq83742 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq83737 eq32
    | exact resolve eq32 eq83737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq83737
  have eq83824 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq83742
    | exact resolve eq83742 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq83742
  have eq83825 : y = (M.op x y) ∨ x = y := by grind
  clear eq83824
  have eq83855 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq83825
       grind)
    | exact superpose eq83825 eq18
    | exact resolve eq18 eq83825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83856 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq83825
       grind)
    | exact superpose eq83825 eq24
    | exact resolve eq24 eq83825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83902 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq83856
    | exact resolve eq83856 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83856
  have eq84167 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op X0 (k (σ x) (σ y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq83902 eq72677
    | exact resolve eq72677 eq83902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72677
  have eq84170 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq84167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84167
  have eq84678 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq83855 eq4303
    | exact resolve eq4303 eq83855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq84720 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq84678
  have eq84757 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq84720
    | exact resolve eq84720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84720
  have eq84777 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq72578 eq84757
    | exact resolve eq84757 eq72578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72578 eq84757
  have eq84779 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq83825 eq84777
    | exact resolve eq84777 eq83825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83825 eq84777
  have eq84780 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq83902 eq84779
    | exact resolve eq84779 eq83902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84779
  have eq87791 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq84780 eq84170
    | exact resolve eq84170 eq84780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84780
  have eq87803 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq87791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87791
  have eq89213 : x = (M.op (M.op x y) x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87803 eq26
    | (have j1 := eq87803 (σ x)
       grind)
    | exact resolve eq26 eq87803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87803
  have eq89548 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq89213 eq1434
    | exact resolve eq1434 eq89213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434 eq89213
  have eq92425 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83855
       have i₂ := eq89548 sF0
       grind)
    | exact superpose eq89548 eq83855
    | exact resolve eq83855 eq89548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83855 eq89548
  have eq92762 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq92425
  have eq92845 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92762
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq92762
    | exact resolve eq92762 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92762
  have eq92859 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq92845 eq1026
    | exact resolve eq1026 eq92845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq92845
  have eq93017 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92859 eq36
    | exact resolve eq36 eq92859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq92859
  have eq93118 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq93017
    | exact resolve eq93017 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93017
  have eq93136 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq83902 eq93118
    | exact resolve eq93118 eq83902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93118
  have eq93756 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq93136 eq84170
    | exact resolve eq84170 eq93136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84170 eq93136
  have eq93770 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq93756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93756
  have eq94301 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93770 eq26
    | (have j1 := eq93770 (σ x)
       grind)
    | exact resolve eq26 eq93770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93770
  have eq94312 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq94301
  have eq94495 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq94312 eq27
    | exact resolve eq27 eq94312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94312
  have eq94747 : x = y := by
    first
    | (have r₁ := eq94495
       have r₂ := eq83902
       grind)
    | exact resolve eq94495 eq83902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83902 eq94495
  have eq94796 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq94747
       grind)
    | exact superpose eq94747 eq18
    | exact resolve eq18 eq94747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq94797 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq94747
       grind)
    | exact superpose eq94747 eq24
    | exact resolve eq24 eq94747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq94747
  have eq94806 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq94797
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94797
    | exact resolve eq94797 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94797
  have eq94807 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq94796
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq94796
    | exact resolve eq94796 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94796
  have eq94808 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq94806 eq26
    | exact resolve eq26 eq94806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq94806
  have eq94896 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq94808
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq94808
    | exact resolve eq94808 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq94808
  have eq94910 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq94807
       grind)
    | exact superpose eq94807 eq40
    | exact resolve eq40 eq94807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq94807
  have eq94935 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq94910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94910
    | exact resolve eq94910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94910
  have eq94940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq94896 eq94935
    | exact resolve eq94935 eq94896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94896 eq94935
  have eq94943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq94940
    | exact resolve eq94940 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq94940
  have eq94945 : False := by grind
  exact eq94945

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4502 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq123 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X2 X2) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 (M.op X1 X1)
       have i₂ := eq14 (M.op X1 X1) X1 X2 x
       grind)
    | exact superpose eq14 eq114
    | exact resolve eq114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq212 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X2 X3
       have i₂ := eq56 (M.op X0 X0) X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1 x x
       have i₂ := eq56 (M.op x x) X0
       grind)
    | exact superpose eq56 eq217
    | exact resolve eq217 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq393 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op x y) X0) ∨ (M.op X1 X1) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq13
    | (have j0 := eq13 X1 (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) X0)
       have r₂ := eq221 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq13 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq400 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq680 : ∀ X2 : G, (M.op (M.op x y) X2) = (k (M.op X2 X2) (M.op (M.op x y) X2)) := by
    intro X2
    first
    | (have i₁ := eq123 x x X2
       have i₂ := eq212 x x X2
       grind)
    | (have i₁ := eq123 x y X2
       have i₂ := eq212 x x X2
       grind)
    | exact superpose eq212 eq123
    | (have j0 := eq123 x y X2
       grind)
    | exact resolve eq123 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq893 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq914 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq893 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq919 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq914 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq914 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq914 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq3271 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq680 eq919
    | (have j0 := eq919 (M.op (M.op x y) (M.op x y)) X0
       grind)
    | exact resolve eq919 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq919
  have eq3284 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3342 : ∀ X0 : G, (k (τ X0) (M.op (M.op x y) (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3284 eq298
    | exact resolve eq298 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq3347 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq3284 eq36
    | exact resolve eq36 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3348 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq3284 eq37
    | exact resolve eq37 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3284
  have eq3369 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq400 eq3348
    | exact resolve eq3348 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3370 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq400 eq3347
    | exact resolve eq3347 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347
  have eq3388 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3369
       grind)
    | exact superpose eq3369 eq16
    | exact resolve eq16 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3415 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3370
       grind)
    | exact superpose eq3370 eq16
    | exact resolve eq16 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq4307 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq190
  have eq4313 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4307
  have eq4316 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4313
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq4313
    | exact resolve eq4313 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4313
  have eq4398 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4316
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4316 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4559 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4398 eq106
    | exact resolve eq106 eq4398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4565 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq3388 eq4559
    | exact resolve eq4559 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4607 : (τ (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) = (k (k y y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq106 eq3342
    | exact resolve eq3342 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq4614 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq400 eq3342
    | exact resolve eq3342 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq4689 : (M.op (k y y) (k y y)) = (τ (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    first
    | exact superpose eq400 eq4607
    | exact resolve eq4607 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq4607
  have eq4712 : (M.op (k y y) (k y y)) = (τ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq4398 eq4689
    | exact resolve eq4689 eq4398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4398 eq4689
  have eq4726 : (M.op (k y y) (k y y)) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq4712
       have i₂ := eq56 (M.op sF3 sF3) sF3
       grind)
    | exact superpose eq56 eq4712
    | exact resolve eq4712 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq4731 : (M.op (M.op y y) (M.op y y)) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq4726
       have i₂ := eq4565
       grind)
    | exact superpose eq4565 eq4726
    | exact resolve eq4726 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565 eq4726
  have eq4733 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq4731
       have i₂ := eq56 (M.op y y) y
       grind)
    | exact superpose eq56 eq4731
    | exact resolve eq4731 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4731
  have eq4735 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq4733 eq15
    | exact resolve eq15 eq4733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4907 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4614 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4614
    | exact resolve eq4614 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614
  have eq5572 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq4907 X0
       grind)
    | exact superpose eq4907 eq15
    | exact resolve eq15 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq6689 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (σ X0) (σ X0) X1
       have i₂ := eq5572 X0
       grind)
    | exact superpose eq5572 eq212
    | exact resolve eq212 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq38499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq38500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq38499
    | exact resolve eq38499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38499
  have eq38511 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq38500
       have r₂ := eq28
       grind)
    | exact resolve eq38500 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38500
  have eq38515 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38511 eq3388
    | exact resolve eq3388 eq38511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq38511
  have eq38557 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq38515
    | exact resolve eq38515 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38515
  have eq38558 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq38557
  have eq38564 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38558 eq3415
    | exact resolve eq3415 eq38558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415 eq38558
  have eq38607 : x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq38564
    | exact resolve eq38564 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38564
  have eq38608 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq38607
  have eq38630 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6689 y X0
       have i₂ := eq38608
       grind)
    | exact superpose eq38608 eq6689
    | exact resolve eq6689 eq38608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38635 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq212 y y X0
       have i₂ := eq38608
       grind)
    | exact superpose eq38608 eq212
    | exact resolve eq212 eq38608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38608
  have eq38641 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq38630 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38630
    | (have j0 := eq38630 X0
       grind)
    | exact resolve eq38630 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38630
  have eq39288 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38635 eq4735
    | exact resolve eq4735 eq38635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38635
  have eq39356 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39288
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq39288
    | exact resolve eq39288 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39288
  have eq39368 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq39356
    | exact resolve eq39356 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39356
  have eq41869 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq38641
    | (have j0 := eq38641 (σ y)
       grind)
    | exact resolve eq38641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38641
  have eq41977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41869 eq39368
    | exact resolve eq39368 eq41869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39368 eq41869
  have eq42026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq41977
  have eq42034 : x = (M.op x x) := by
    first
    | (have r₁ := eq42026
       have r₂ := eq28
       grind)
    | exact resolve eq42026 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42026
  have eq42057 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq6689 x X0
       have i₂ := eq42034
       grind)
    | exact superpose eq42034 eq6689
    | exact resolve eq6689 eq42034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq42062 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq212 x x X0
       have i₂ := eq42034
       grind)
    | exact superpose eq42034 eq212
    | exact resolve eq212 eq42034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq42034
  have eq42069 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq42057 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42057
    | (have j0 := eq42057 X0
       grind)
    | exact resolve eq42057 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq42057
  have eq43205 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq42062 eq4735
    | exact resolve eq4735 eq42062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq43302 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq42062 eq43205
    | exact resolve eq43205 eq42062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43205
  have eq43361 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq43302
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43302
    | exact resolve eq43302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq43302
  have eq43372 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21 eq43361
    | exact resolve eq43361 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43361
  have eq43878 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq42062 eq42069
    | exact resolve eq42069 eq42062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42062 eq42069
  have eq43957 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq43878 eq27
    | (have j1 := eq43878 (σ y)
       grind)
    | exact resolve eq27 eq43878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq43878
  have eq44010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43372 eq43957
    | exact resolve eq43957 eq43372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43372 eq43957
  have eq44034 : False := by grind
  exact eq44034

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pxx_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq98 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq99 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op x x)
       have i₂ := eq55 (M.op x x) x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq55 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq359 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq213 eq13
    | (have r₁ := eq13 (M.op (M.op x y) y) x
       have r₂ := eq213 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq370 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq215 (M.op x X1) X1
       have i₂ := eq215 x X1
       grind)
    | (have i₁ := eq215 (M.op x y) y
       have i₂ := eq215 x X1
       grind)
    | exact superpose eq215 eq215
    | exact resolve eq215 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq364 eq38
    | exact resolve eq38 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq918 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq97 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq919 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq3130 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq919 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq919
    | (have j0 := eq919 (τ X0)
       grind)
    | exact resolve eq919 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3142 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3130 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3130
    | (have j0 := eq3130 X0
       grind)
    | exact resolve eq3130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq3149 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3142 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3142
    | (have j0 := eq3142 X0
       grind)
    | exact resolve eq3142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq3469 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 x
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3479 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3469
  have eq3485 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3479
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3479
    | exact resolve eq3479 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3479
  have eq3502 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3485
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq3485 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq3508 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3502 eq49
    | exact resolve eq49 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3502
  have eq3652 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99
    | (have j0 := eq99 y
       grind)
    | exact resolve eq99 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq3661 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3652
  have eq3666 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3661
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq3661
    | exact resolve eq3661 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3661
  have eq3690 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3666
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq3666 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3705 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3690 eq91
    | exact resolve eq91 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3690
  have eq3967 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq3975 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3967
  have eq3979 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq3975
    | exact resolve eq3975 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq3975
  have eq4010 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3979
       have r₂ := eq13 (σ (M.op x y)) x
       grind)
    | exact resolve eq3979 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq10855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq10856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq10855
    | exact resolve eq10855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10855
  have eq10867 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq10856
       have r₂ := eq27
       grind)
    | exact resolve eq10856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10856
  have eq10869 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq10867
    | exact resolve eq10867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10867
  have eq10871 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10869 eq3705
    | exact resolve eq3705 eq10869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10892 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq10871
    | exact resolve eq10871 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10871
  have eq10893 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3149 y
       grind)
    | (have r₁ := eq10892
       have r₂ := eq3149 y
       grind)
    | exact resolve eq10892 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149 eq10892
  have eq10895 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 y
       have i₂ := eq10893
       grind)
    | exact superpose eq10893 eq55
    | exact resolve eq55 eq10893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10896 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10893
       grind)
    | exact superpose eq10893 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq10893
       grind)
    | exact resolve eq13 eq10893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10900 : ∀ X0 : G, y = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10896
  have eq10908 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq919 y
       have i₂ := eq10900 y
       grind)
    | exact superpose eq10900 eq919
    | (have j0 := eq919 y
       grind)
    | exact resolve eq919 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq10920 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq10900 (τ X0)
       grind)
    | exact superpose eq10900 eq38
    | exact resolve eq38 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10900
  have eq10959 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10908
  have eq10999 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10920 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10920
    | (have j0 := eq10920 X0
       grind)
    | exact resolve eq10920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10920
  have eq11004 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10959
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10959
    | exact resolve eq10959 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10959
  have eq11254 : ∀ X0 : G, (σ (σ y)) = (k (σ (σ y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10999 eq38
    | exact resolve eq38 eq10999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq11472 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11004 eq55
    | exact resolve eq55 eq11004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11944 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10895 X0
       have i₂ := eq10895 sF0
       grind)
    | exact superpose eq10895 eq10895
    | exact resolve eq10895 eq10895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq11972 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq11944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944
  have eq12061 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11972 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11972
    | (have j0 := eq11972 x X0
       grind)
    | exact resolve eq11972 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12117 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10893
       have i₂ := eq11972 y X0
       grind)
    | (have i₁ := eq10893
       have i₂ := eq11972 X0 y
       grind)
    | exact superpose eq11972 eq10893
    | exact resolve eq10893 eq11972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10893
  have eq12134 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq14615 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11472
    | (have j0 := eq11472 (σ x)
       grind)
    | exact resolve eq11472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14639 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11472 eq12061
    | exact resolve eq12061 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14668 : (σ y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11472 eq11004
    | exact resolve eq11004 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11004
  have eq14671 : (σ y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14668
  have eq14681 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14733 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14615 eq11472
    | exact resolve eq11472 eq14615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11472 eq14615
  have eq14751 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14733
  have eq15213 : y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14671 eq12134
    | exact resolve eq12134 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134
  have eq15214 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14671 eq12061
    | exact resolve eq12061 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12061
  have eq15216 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14671 eq11972
    | exact resolve eq11972 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11972 eq14671
  have eq15222 : ∀ X0 : G, (σ y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15216
  have eq15224 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq15214
  have eq15225 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq15213
  have eq15694 : ∀ X0 : G, (M.op x y) ≠ (σ y) ∨ (M.op x y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14681 eq13
    | exact resolve eq13 eq14681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14681
  have eq15737 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15694 X0
       grind)
    | (have r₁ := eq15694 X0
       have r₂ := eq15224
       grind)
    | exact resolve eq15694 eq15224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15224 eq15694
  have eq16529 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14751 eq3705
    | exact resolve eq3705 eq14751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705 eq14751
  have eq17093 : ∀ X0 : G, y ≠ (σ y) ∨ (σ y) = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15222 y
       grind)
    | exact superpose eq15222 eq13
    | exact resolve eq13 eq15222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15222
  have eq17168 : ∀ X0 : G, (σ y) = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17093 X0
       grind)
    | (have r₁ := eq17093 X0
       have r₂ := eq15225
       grind)
    | exact resolve eq17093 eq15225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225 eq17093
  have eq17579 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (σ y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15737 eq38
    | exact resolve eq38 eq15737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq15737
  have eq17634 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (σ y)) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq17579
    | (have j0 := eq17579 X0
       grind)
    | exact resolve eq17579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17579
  have eq28418 : (σ y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17168 y
       have i₂ := eq16529
       grind)
    | exact superpose eq16529 eq17168
    | exact resolve eq17168 eq16529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16529 eq17168
  have eq28439 : (σ y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28418
  have eq28553 : (M.op (σ x) (σ y)) = (σ (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28439 eq15
    | exact resolve eq15 eq28439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28439
  have eq29325 : (σ (M.op x y)) = (σ (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17634 eq11254
    | exact resolve eq11254 eq17634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254 eq17634
  have eq29383 : (σ (M.op x y)) = (σ (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29325
  have eq29427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29383 eq28553
    | exact resolve eq28553 eq29383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28553 eq29383
  have eq29496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29427
  have eq29511 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq29496
       have r₂ := eq27
       grind)
    | exact resolve eq29496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29496
  have eq29527 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29511 eq225
    | exact resolve eq225 eq29511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq29560 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq29527
    | exact resolve eq29527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29527
  have eq29577 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29560 eq213
    | exact resolve eq213 eq29560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq29581 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29560 eq370
    | exact resolve eq370 eq29560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29560
  have eq29649 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29511 eq29577
    | exact resolve eq29577 eq29511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29577
  have eq29699 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649
  have eq29765 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29511 eq29581
    | exact resolve eq29581 eq29511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29511 eq29581
  have eq29853 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29765
  have eq29871 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29699 (M.op x sF2)
       have i₂ := eq215 x sF2
       grind)
    | exact superpose eq215 eq29699
    | exact resolve eq29699 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29901 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29699 eq3508
    | exact resolve eq3508 eq29699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq29699
  have eq29949 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq29901
    | exact resolve eq29901 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29901
  have eq30327 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq29949
       grind)
    | exact superpose eq29949 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq29949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29949
  have eq30328 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq30327
  have eq30665 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x
       have i₂ := eq30328
       grind)
    | exact superpose eq30328 eq55
    | exact resolve eq55 eq30328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq49608 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30665 eq29871
    | exact resolve eq29871 eq30665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29871 eq30665
  have eq49673 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq49608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49608
  have eq49773 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30328
       have i₂ := eq49673 x
       grind)
    | exact superpose eq49673 eq30328
    | exact resolve eq30328 eq49673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30328 eq49673
  have eq49800 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq49773
  have eq50260 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49800 eq29853
    | exact resolve eq29853 eq49800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29853 eq49800
  have eq50291 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq50260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50260
  have eq55304 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq50291 y
       grind)
    | exact superpose eq50291 eq18
    | (have j1 := eq50291 y
       grind)
    | exact resolve eq18 eq50291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50291
  have eq55402 : x = (M.op x y) := by grind
  clear eq55304
  have eq55825 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq55402 eq20
    | exact resolve eq20 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55884 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq55402 eq370
    | exact resolve eq370 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq55885 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq55402 eq448
    | exact resolve eq448 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq55978 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq55885 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55885
    | (have j0 := eq55885 X0
       grind)
    | exact resolve eq55885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55885
  have eq55979 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq55884 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55884
    | (have j0 := eq55884 X0
       grind)
    | exact resolve eq55884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55884
  have eq56034 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq55825
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55825
    | exact resolve eq55825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq55825
  have eq56045 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq55978
    | (have j0 := eq55978 X0
       grind)
    | exact resolve eq55978 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55978
  have eq56046 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq55402 eq55979
    | exact resolve eq55979 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55979
  have eq56096 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq56034 eq26
    | exact resolve eq26 eq56034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq56034
  have eq56322 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4010 eq56045
    | exact resolve eq56045 eq4010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010 eq56045
  have eq58992 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq56322 eq215
    | exact resolve eq215 eq56322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq58996 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq56322 eq58992
    | exact resolve eq58992 eq56322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56322 eq58992
  have eq59012 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq55402 eq58996
    | exact resolve eq58996 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58996
  have eq59029 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq59012
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59012
    | exact resolve eq59012 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq59012
  have eq59045 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq55402 eq59029
    | exact resolve eq59029 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55402 eq59029
  have eq59150 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq59045 eq56096
    | exact resolve eq56096 eq59045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56096
  have eq59153 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59150
       have i₂ := eq56046 sF3
       grind)
    | exact superpose eq56046 eq59150
    | exact resolve eq59150 eq56046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56046 eq59150
  have eq59415 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq59153 eq27
    | exact resolve eq27 eq59153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq59153
  have eq59485 : False := by grind
  exact eq59485

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x x) X4 X5
       have i₂ := eq16 (M.op x x) x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x (M.op X1 X1)) X1 x x
       have i₂ := eq16 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
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
  have eq184 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq183 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op x x)
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
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
  have eq196 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x x) X2 X3
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq225 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq207 eq184
    | exact resolve eq184 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq184 eq13
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have r₂ := eq184 x
       grind)
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq239 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq207 eq237
    | exact resolve eq237 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq237
  have eq488 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq239 eq38
    | exact resolve eq38 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq239
  have eq1153 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq1161 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq1166 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1236 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq488 eq1167
    | (have j0 := eq1167 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq1167 (σ (M.op (M.op x y) y))
       have r₂ := eq488 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq1167 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq1245 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq1236
  have eq2295 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1153
       grind)
    | exact superpose eq1153 eq39
    | exact resolve eq39 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2295
    | exact resolve eq2295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2298 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2296
    | exact resolve eq2296 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq16066 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq1245 eq196
    | exact resolve eq196 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq16070 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1245 eq16066
    | exact resolve eq16066 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245 eq16066
  have eq16082 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq191 eq16070
    | exact resolve eq16070 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq16070
  have eq16110 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16082 eq15
    | exact resolve eq15 eq16082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2298 eq1161
    | exact resolve eq1161 eq2298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18856 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18848
       have r₂ := eq27
       grind)
    | exact resolve eq18848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18848
  have eq18912 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18856 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18856
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq18856
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq18856
       grind)
    | exact resolve eq13 eq18856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18856
  have eq18920 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq18912
  have eq18928 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2298 eq18920
    | exact resolve eq18920 eq2298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298 eq18920
  have eq18947 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18928 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq18928
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq18928
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18928
       grind)
    | exact resolve eq13 eq18928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928
  have eq18955 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq18947
  have eq18976 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18955 eq141
    | exact resolve eq141 eq18955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq18955
  have eq18984 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq18976
    | exact resolve eq18976 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18976
  have eq18989 : y = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq1167 x
       grind)
    | (have r₁ := eq18984
       have r₂ := eq1167 x
       grind)
    | exact resolve eq18984 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq18984
  have eq18996 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 y x X2 X0 X1
       have i₂ := eq18989
       grind)
    | exact superpose eq18989 eq174
    | exact resolve eq174 eq18989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19000 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq195 y x
       have i₂ := eq18989
       grind)
    | exact superpose eq18989 eq195
    | exact resolve eq195 eq18989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19004 : y = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18989 eq19000
    | exact resolve eq19000 eq18989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19000
  have eq19008 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq18996 x x X2
       have i₂ := eq195 x x
       grind)
    | (have i₁ := eq18996 x y X2
       have i₂ := eq195 X2 x
       grind)
    | exact superpose eq195 eq18996
    | (have j0 := eq18996 x y X2
       grind)
    | exact resolve eq18996 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19016 : ∀ X2 : G, y = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq19004 eq19008
    | exact resolve eq19008 eq19004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19008
  have eq19018 : ∀ X2 : G, y = (M.op X2 y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq18989 eq19016
    | exact resolve eq19016 eq18989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18989 eq19016
  have eq19073 : y = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19004 eq16082
    | exact resolve eq16082 eq19004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19004
  have eq19120 : x = (M.op x x) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19073
    | exact resolve eq19073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19073
  have eq19179 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq195 x x
       have i₂ := eq19120
       grind)
    | exact superpose eq19120 eq195
    | exact resolve eq195 eq19120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19185 : x = (M.op (M.op x y) y) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19120 eq19179
    | exact resolve eq19179 eq19120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19120 eq19179
  have eq19222 : ∀ X0 : G, x = (M.op x X0) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq19185 eq225
    | exact resolve eq225 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19254 : x = (σ x) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19185 eq16082
    | exact resolve eq16082 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19293 : x = (M.op x y) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19185 eq195
    | exact resolve eq195 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19302 : (σ (M.op x y)) = (σ y) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19293
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19293
    | exact resolve eq19293 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19293
  have eq19309 : x = (σ x) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19254
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19254
    | exact resolve eq19254 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254
  have eq19344 : (σ (M.op x y)) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq19302 eq19309
    | exact resolve eq19309 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19309
  have eq19361 : (M.op x y) = (τ (σ y)) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19302 eq28
    | exact resolve eq28 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19461 : y = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq19361
    | exact resolve eq19361 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19361
  have eq19472 : (M.op x y) = (τ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq19344 eq28
    | exact resolve eq28 eq19344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19344
  have eq19572 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq19472
    | exact resolve eq19472 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19472
  have eq19714 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19572 eq26
    | exact resolve eq26 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19715 : x = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19572 eq29
    | exact resolve eq29 eq19572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19572
  have eq19822 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19461 eq19715
    | exact resolve eq19715 eq19461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19461 eq19715
  have eq20139 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19822 eq14
    | exact resolve eq14 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20188 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20139
    | exact resolve eq20139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20139
  have eq20525 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op x X0) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq195 x X0
       have i₂ := eq19222 X0
       grind)
    | exact superpose eq19222 eq195
    | exact resolve eq195 eq19222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222
  have eq20545 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq19302 eq20525
    | exact resolve eq20525 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20525
  have eq20565 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq19185 eq20545
    | exact resolve eq20545 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185 eq20545
  have eq20578 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq19302 eq20565
    | exact resolve eq20565 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19302 eq20565
  have eq22319 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19714 eq20578
    | exact resolve eq20578 eq19714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19714 eq20578
  have eq22329 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22319
  have eq22335 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20188 eq22329
    | exact resolve eq22329 eq20188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22329
  have eq22632 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22335 eq27
    | exact resolve eq27 eq22335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22335
  have eq22646 : (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22632
       have r₂ := eq20188
       grind)
    | exact resolve eq22632 eq20188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20188 eq22632
  have eq22654 : y = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22646 eq31
    | exact resolve eq31 eq22646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22646
  have eq22789 : y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19822 eq22654
    | exact resolve eq22654 eq19822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19822 eq22654
  have eq22790 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22789
  have eq22829 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22790
       grind)
    | exact superpose eq22790 eq18
    | exact resolve eq18 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22887 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16082
       have i₂ := eq22790
       grind)
    | exact superpose eq22790 eq16082
    | exact resolve eq16082 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22917 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  have eq24934 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19018 x
       grind)
    | exact superpose eq19018 eq18
    | (have j1 := eq19018 x
       grind)
    | exact resolve eq18 eq19018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19018
  have eq25134 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq195 x x
       have i₂ := eq24934
       grind)
    | exact superpose eq24934 eq195
    | exact resolve eq195 eq24934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25143 : (M.op x x) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22790 eq25134
    | exact resolve eq25134 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq25156 : x = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24934 eq25143
    | exact resolve eq25143 eq24934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24934 eq25143
  have eq25199 : x = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25156 eq22887
    | exact resolve eq22887 eq25156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22887
  have eq25209 : (M.op (M.op x y) y) = (M.op x (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25156 eq195
    | exact resolve eq195 eq25156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25214 : x = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25199
  have eq25223 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22790 eq25209
    | exact resolve eq25209 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22790 eq25209
  have eq25230 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq25214
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25214
    | exact resolve eq25214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25214
  have eq25233 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22829 eq25223
    | exact resolve eq25223 eq22829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22829 eq25223
  have eq25248 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq25230 eq28
    | exact resolve eq28 eq25230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25230
  have eq25356 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq31 eq25248
    | exact resolve eq25248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25248
  have eq25357 : y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq25356
  have eq25412 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25357
       grind)
    | exact superpose eq25357 eq24
    | exact resolve eq24 eq25357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25562 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq25412
    | exact resolve eq25412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25412
  have eq25988 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25233 eq25156
    | exact resolve eq25156 eq25233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25156
  have eq26000 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25988
  have eq26016 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq25357 eq26000
    | exact resolve eq26000 eq25357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26000
  have eq26022 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq26016 eq28
    | exact resolve eq28 eq26016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq26016
  have eq26130 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq31 eq26022
    | exact resolve eq26022 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq26022
  have eq26131 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq26130
  have eq26183 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26131 eq26
    | exact resolve eq26 eq26131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26184 : x = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26131 eq29
    | exact resolve eq29 eq26131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26301 : (σ x) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25357 eq26184
    | exact resolve eq26184 eq25357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25357 eq26184
  have eq26352 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26131 eq26301
    | exact resolve eq26301 eq26131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26131 eq26301
  have eq26422 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26352 eq14
    | exact resolve eq14 eq26352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26352
  have eq26479 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq26422
    | exact resolve eq26422 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26422
  have eq26657 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26183 eq25233
    | exact resolve eq25233 eq26183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25233 eq26183
  have eq26669 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26657
  have eq26683 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26479 eq26669
    | exact resolve eq26669 eq26479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26669
  have eq26687 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26683
       have r₂ := eq22917
       grind)
    | exact resolve eq26683 eq22917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22917 eq26683
  have eq26691 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26687 eq27
    | exact resolve eq27 eq26687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26687
  have eq26702 : y = (M.op x y) := by
    first
    | (have r₁ := eq26691
       have r₂ := eq26479
       grind)
    | exact resolve eq26691 eq26479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26479 eq26691
  have eq26707 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq18
    | exact resolve eq18 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26708 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq24
    | exact resolve eq24 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26710 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq40
    | exact resolve eq40 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq26716 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq225 X0
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq225
    | exact resolve eq225 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq26744 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq1153
    | exact resolve eq1153 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq26765 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16082
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq16082
    | exact resolve eq16082 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16082
  have eq26768 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16110
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq16110
    | exact resolve eq16110 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16110
  have eq26832 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq26744
       have r₂ := eq12 x x
       grind)
    | exact resolve eq26744 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26744
  have eq26863 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26708 eq20
    | exact resolve eq20 eq26708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27305 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq26707 eq16
    | exact resolve eq16 eq26707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq26707 eq175
    | exact resolve eq175 eq26707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29851 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq26716 X0
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq26716
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq26716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29921 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq29851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29851
  have eq31217 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26832 eq39
    | exact resolve eq39 eq26832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq26832
  have eq31222 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq31217
    | exact resolve eq31217 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31217
  have eq31228 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26863 eq31222
    | exact resolve eq31222 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31222
  have eq31295 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq31228 eq1161
    | exact resolve eq1161 eq31228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq31228
  have eq53887 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29921 eq27305
    | exact resolve eq27305 eq29921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27305 eq29921
  have eq53925 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq53887
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq53887 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53887
  have eq54025 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq53925 eq26716
    | exact resolve eq26716 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26716
  have eq54029 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53925 eq26765
    | exact resolve eq26765 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26765
  have eq54032 : (k (M.op x y) (M.op x y)) = (τ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53925 eq26768
    | exact resolve eq26768 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26768
  have eq54078 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq53925 eq175
    | exact resolve eq175 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq54083 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq53925 eq27308
    | exact resolve eq27308 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27308
  have eq54087 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq54083 eq54078
    | exact resolve eq54078 eq54083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54078 eq54083
  have eq54104 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq54029
    | exact resolve eq54029 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54029
  have eq54115 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26863 eq54104
    | exact resolve eq54104 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54104
  have eq54118 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq54115
    | exact resolve eq54115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54115
  have eq54120 : (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26863 eq54118
    | exact resolve eq54118 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54118
  have eq446647 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq31295 eq174
    | exact resolve eq174 eq31295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446657 : (k (M.op x y) (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq31295 eq54087
    | exact resolve eq54087 eq31295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446661 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq31295 eq446657
    | exact resolve eq446657 eq31295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446657
  have eq446671 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | (have i₁ := eq446647 x x X2
       have i₂ := eq195 x x
       grind)
    | (have i₁ := eq446647 x y X2
       have i₂ := eq195 X2 x
       grind)
    | exact superpose eq195 eq446647
    | (have j0 := eq446647 x y X2
       grind)
    | exact resolve eq446647 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446647
  have eq446684 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | (have i₁ := eq446671 X2
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq446671
    | exact resolve eq446671 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446671
  have eq446693 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq53925 eq446684
    | exact resolve eq446684 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446684
  have eq446701 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq31295 eq446693
    | exact resolve eq446693 eq31295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31295 eq446693
  have eq446704 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq446661 eq446701
    | exact resolve eq446701 eq446661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446661 eq446701
  have eq486600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq446704 eq26
    | (have j1 := eq446704 (σ x)
       grind)
    | exact resolve eq26 eq446704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446704
  have eq486610 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq486600
  have eq486647 : (k (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq486610 eq54087
    | exact resolve eq54087 eq486610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486652 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq486610 eq486647
    | exact resolve eq486647 eq486610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486610 eq486647
  have eq486876 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq486652 eq54025
    | exact resolve eq54025 eq486652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54025
  have eq486881 : (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq486652 eq54032
    | exact resolve eq54032 eq486652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54032 eq486652
  have eq487288 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq486881
    | exact resolve eq486881 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq486881
  have eq487453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X0 X1 X2
    first
    | exact superpose eq487288 eq174
    | exact resolve eq174 eq487288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq487462 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq487288 eq54087
    | exact resolve eq54087 eq487288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487465 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq487288 eq487462
    | exact resolve eq487462 eq487288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487462
  have eq487474 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | (have i₁ := eq487453 x x X2
       have i₂ := eq195 x x
       grind)
    | (have i₁ := eq487453 x y X2
       have i₂ := eq195 X2 x
       grind)
    | exact superpose eq195 eq487453
    | (have j0 := eq487453 x y X2
       grind)
    | exact resolve eq487453 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq487453
  have eq487486 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | (have i₁ := eq487474 X2
       have i₂ := eq26702
       grind)
    | exact superpose eq26702 eq487474
    | exact resolve eq487474 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26702 eq487474
  have eq487493 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq53925 eq487486
    | exact resolve eq487486 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53925 eq487486
  have eq487499 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq487465 eq487493
    | exact resolve eq487493 eq487465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487493
  have eq487501 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    intro X2
    first
    | exact superpose eq487288 eq487499
    | exact resolve eq487499 eq487288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487288 eq487499
  have eq488083 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq487465 eq26710
    | exact resolve eq26710 eq487465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq488083
    | exact resolve eq488083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488083
  have eq488215 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq26863 eq488181
    | exact resolve eq488181 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488181
  have eq488247 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq54120 eq488215
    | exact resolve eq488215 eq54120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488215
  have eq488277 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq487465 eq488247
    | exact resolve eq488247 eq487465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487465 eq488247
  have eq488401 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq488277 eq27
    | exact resolve eq27 eq488277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488277
  have eq488453 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq488401
       have r₂ := eq25562
       grind)
    | exact resolve eq488401 eq25562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25562 eq488401
  have eq488461 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq488453 eq26
    | exact resolve eq26 eq488453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490985 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq487501 eq488461
    | exact resolve eq488461 eq487501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487501 eq488461
  have eq490992 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq490985
  have eq491037 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq488453 eq490992
    | exact resolve eq490992 eq488453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490992
  have eq491038 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq491037
  have eq497225 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq491038 eq27
    | exact resolve eq27 eq491038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491038
  have eq497280 : (M.op x y) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq26863 eq497225
    | exact resolve eq497225 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497225
  have eq497291 : x = (σ x) := by
    first
    | (have r₁ := eq497280
       have r₂ := eq488453
       grind)
    | exact resolve eq497280 eq488453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488453 eq497280
  have eq497300 : (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq22
       have i₂ := eq497291
       grind)
    | exact superpose eq497291 eq22
    | exact resolve eq22 eq497291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq497425 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq26707
       have i₂ := eq497291
       grind)
    | exact superpose eq497291 eq26707
    | exact resolve eq26707 eq497291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26707
  have eq508556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq486876 eq26
    | (have j1 := eq486876 (σ y)
       grind)
    | exact resolve eq26 eq486876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486876
  have eq508669 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq508556
       have i₂ := eq497291
       grind)
    | exact superpose eq497291 eq508556
    | exact resolve eq508556 eq497291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497291 eq508556
  have eq508818 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq508669 eq54087
    | exact resolve eq54087 eq508669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54087
  have eq508821 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq508669 eq508818
    | exact resolve eq508818 eq508669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508669 eq508818
  have eq516258 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq508821 eq26710
    | exact resolve eq26710 eq508821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26710
  have eq516341 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq516258
    | exact resolve eq516258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516258
  have eq516376 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26863 eq516341
    | exact resolve eq516341 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516341
  have eq516408 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54120 eq516376
    | exact resolve eq516376 eq54120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54120 eq516376
  have eq516438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq508821 eq516408
    | exact resolve eq516408 eq508821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508821 eq516408
  have eq516563 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq516438 eq27
    | exact resolve eq27 eq516438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516438
  have eq516621 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq516563
       have r₂ := eq26863
       grind)
    | exact resolve eq516563 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516563
  have eq516635 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq516621 eq184
    | exact resolve eq184 eq516621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq516689 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq516635
    | (have j0 := eq516635 X0
       grind)
    | exact resolve eq516635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516635
  have eq516702 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq516621 eq516689
    | exact resolve eq516689 eq516621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516621 eq516689
  have eq517614 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq516702 eq497425
    | exact resolve eq497425 eq516702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516702
  have eq517841 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq517614 eq26
    | exact resolve eq26 eq517614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518423 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq497425 eq517841
    | exact resolve eq517841 eq497425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517841
  have eq518620 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq518423 eq27
    | exact resolve eq27 eq518423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518423
  have eq518679 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq26863 eq518620
    | exact resolve eq518620 eq26863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26863 eq518620
  have eq518690 : (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq518679
       have r₂ := eq517614
       grind)
    | exact resolve eq518679 eq517614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517614 eq518679
  have eq518957 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq518690 eq497300
    | exact resolve eq497300 eq518690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497300 eq518690
  have eq520030 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq518957 eq26708
    | exact resolve eq26708 eq518957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26708
  have eq520031 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq518957 eq20
    | exact resolve eq20 eq518957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq518957
  have eq521911 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq520030 eq26
    | exact resolve eq26 eq520030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq520030
  have eq522467 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq497425 eq521911
    | exact resolve eq521911 eq497425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497425 eq521911
  have eq523134 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq522467 eq27
    | exact resolve eq27 eq522467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq522467
  have eq523189 : False := by grind
  exact eq523189
