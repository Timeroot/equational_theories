import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq450 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2997 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq450 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450
    | exact resolve eq450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq3051 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2997 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2997
    | (have j0 := eq2997 X0 X1
       grind)
    | exact resolve eq2997 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3055 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3051 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3051
    | (have j0 := eq3051 (τ X1) (τ X0)
       grind)
    | exact resolve eq3051 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq3148 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3055 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3055
    | (have j0 := eq3055 X0 X1
       grind)
    | exact resolve eq3055 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq18460 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3148 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3148 X0 X1
       grind)
    | exact superpose eq3148 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3148 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3148 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3148 X0 X1
       grind)
    | exact resolve eq13 eq3148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq18471 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18460 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18460
  have eq18472 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18471
  have eq18480 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18472 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq18472
    | (have j0 := eq18472 X0 X1
       grind)
    | exact resolve eq18472 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18472
  have eq31226 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18480 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18480
    | exact resolve eq18480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18480
  have eq31317 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31226 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq31226
    | (have j0 := eq31226 X0 X1
       grind)
    | exact resolve eq31226 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31226
  have eq31390 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq31317 X0 X1
       grind)
    | exact superpose eq31317 eq10
    | (have j1 := eq31317 X0 X1
       grind)
    | exact resolve eq10 eq31317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31317
  have eq31504 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31390 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq31390
    | (have j0 := eq31390 X0 X1
       grind)
    | exact resolve eq31390 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq31390
  have eq31505 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31504
  have eq31535 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31505 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31505
    | exact resolve eq31505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31591 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq31505 X1 X0
       grind)
    | exact superpose eq31505 eq19
    | (have j1 := eq31505 X1 X0
       grind)
    | exact resolve eq19 eq31505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq31505
  have eq31991 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq31535 (σ X0) (σ X1)
       grind)
    | exact superpose eq31535 eq15
    | (have j1 := eq31535 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq31535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31535
  have eq32143 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31591 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31591
    | exact resolve eq31591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31591
  have eq32327 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32143 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq32143
    | (have j0 := eq32143 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq32143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32143
  have eq33923 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31991 x y
       grind)
    | exact superpose eq31991 eq16
    | (have j1 := eq31991 x y
       grind)
    | exact resolve eq16 eq31991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31991
  have eq33993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33923
       have i₂ := eq32327 x y
       grind)
    | exact superpose eq32327 eq33923
    | (have j1 := eq32327 (σ x) (σ y)
       grind)
    | (have r₁ := eq33923
       have r₂ := eq32327 x y
       grind)
    | (have r₁ := eq33923
       have r₂ := eq32327 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq33923
       have r₂ := eq32327 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq33923 eq32327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32327 eq33923
  have eq33999 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq33993
  have eq34002 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33999
       grind)
    | exact superpose eq33999 eq16
    | exact resolve eq16 eq33999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33999
  have eq34003 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq34002
       have r₂ := eq22 x
       grind)
    | exact resolve eq34002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34002
  have eq34004 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34003
       grind)
    | exact superpose eq34003 eq16
    | exact resolve eq16 eq34003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34005 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq34003
       grind)
    | exact superpose eq34003 eq10
    | exact resolve eq10 eq34003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34003
  have eq34177 : x = y := by
    first
    | (have i₁ := eq34005
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34005
    | exact resolve eq34005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34005
  have eq34178 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34004
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq34004
    | exact resolve eq34004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq34004
  have eq34179 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq34178
       have i₂ := eq34177
       grind)
    | exact superpose eq34177 eq34178
    | exact resolve eq34178 eq34177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34177 eq34178
  have eq34180 : False := by grind
  exact eq34180

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq467 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  have eq470 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq3191 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq470
    | exact resolve eq470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq3236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3191 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3191
    | (have j0 := eq3191 X0 X1
       grind)
    | exact resolve eq3191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3503 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq467 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq467 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq467 (σ X1) X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq467 X0 X1
       grind)
    | exact resolve eq13 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3505 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467 (σ x) y
       grind)
    | exact superpose eq467 eq16
    | (have j1 := eq467 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq467 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq3512 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3503 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq3513 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3512 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512
  have eq3518 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3505
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3505
    | exact resolve eq3505 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq3531 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3518
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3518
    | exact resolve eq3518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq3752 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3513 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3513
    | exact resolve eq3513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3843 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3752 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3752
    | (have j0 := eq3752 X0 X1
       grind)
    | exact resolve eq3752 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3752
  have eq3926 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3843 X1 X0
       grind)
    | exact superpose eq3843 eq11
    | (have j1 := eq3843 X1 X0
       grind)
    | exact resolve eq11 eq3843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq4045 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3926 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3926
    | (have j0 := eq3926 X0 X1
       grind)
    | exact resolve eq3926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3926
  have eq4065 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4045 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4045
    | (have j0 := eq4045 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq4045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4114 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq4045 X0 (τ X1)
       grind)
    | exact superpose eq4045 eq18
    | (have j1 := eq4045 X0 (τ X1)
       grind)
    | exact resolve eq18 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4045
  have eq4223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4065 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4065
    | (have j0 := eq4065 X0 X1
       grind)
    | exact resolve eq4065 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4336 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4114 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4114
    | exact resolve eq4114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4336 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4336
    | (have j0 := eq4336 X0 X1
       grind)
    | exact resolve eq4336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq12499 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4223 y x
       grind)
    | exact superpose eq4223 eq16
    | (have j1 := eq4223 y x
       grind)
    | exact resolve eq16 eq4223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq12576 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12499
       have i₂ := eq3236 y x
       grind)
    | exact superpose eq3236 eq12499
    | (have j1 := eq3236 y x
       grind)
    | (have r₁ := eq12499
       have r₂ := eq3236 y x
       grind)
    | (have r₁ := eq12499
       have r₂ := eq3236 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq12499
       have r₂ := eq3236 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq12499 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12499
  have eq12577 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12576
  have eq12703 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12577
       grind)
    | exact superpose eq12577 eq16
    | exact resolve eq16 eq12577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577
  have eq12704 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12703
       have r₂ := eq22 x
       grind)
    | exact resolve eq12703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12703
  have eq12705 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3531
       have i₂ := eq12704
       grind)
    | exact superpose eq12704 eq3531
    | (have r₁ := eq3531
       have r₂ := eq12704
       grind)
    | exact resolve eq3531 eq12704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12704
  have eq12714 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12705
  have eq12715 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq12714
  have eq12716 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq12715
       have r₂ := eq3531
       grind)
    | exact resolve eq12715 eq3531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531 eq12715
  have eq12718 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12716
       grind)
    | exact superpose eq12716 eq10
    | exact resolve eq10 eq12716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12716
  have eq12785 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12718
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12718
    | exact resolve eq12718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12718
  have eq13099 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12785
       grind)
    | exact superpose eq12785 eq16
    | exact resolve eq16 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12785
  have eq13100 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq13099
       have r₂ := eq22 x
       grind)
    | exact resolve eq13099 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13099
  have eq13113 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq13100
       grind)
    | exact superpose eq13100 eq11
    | exact resolve eq11 eq13100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13100
  have eq13202 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13113
       grind)
    | exact superpose eq13113 eq16
    | exact resolve eq16 eq13113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13113
  have eq13233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13202
       have i₂ := eq4388 y x
       grind)
    | exact superpose eq4388 eq13202
    | (have j1 := eq4388 y x
       grind)
    | (have r₁ := eq13202
       have r₂ := eq4388 y x
       grind)
    | (have r₁ := eq13202
       have r₂ := eq4388 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq13202
       have r₂ := eq4388 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq13202 eq4388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4388
  have eq13234 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq13202
       have i₂ := eq3236 y x
       grind)
    | exact superpose eq3236 eq13202
    | (have j1 := eq3236 y x
       grind)
    | (have r₁ := eq13202
       have r₂ := eq3236 y x
       grind)
    | (have r₁ := eq13202
       have r₂ := eq3236 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq13202
       have r₂ := eq3236 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq13202 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq13235 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq13234
  have eq13236 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq13233
  have eq13253 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13202
       have i₂ := eq13236
       grind)
    | exact superpose eq13236 eq13202
    | exact resolve eq13202 eq13236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13254 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq13253
  have eq13255 : (k y x) = (M.op x x) := by grind
  clear eq13254
  have eq13264 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13202
       have i₂ := eq13255
       grind)
    | exact superpose eq13255 eq13202
    | exact resolve eq13202 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13202 eq13255
  have eq13299 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13264
       have i₂ := eq13235
       grind)
    | exact superpose eq13235 eq13264
    | exact resolve eq13264 eq13235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13302 : x = y := by grind
  clear eq13299
  have eq13312 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq13264
       have i₂ := eq13302
       grind)
    | exact superpose eq13302 eq13264
    | exact resolve eq13264 eq13302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13264 eq13302
  have eq13313 : False := by grind
  exact eq13313

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X0 (M.op X0 X0))) X0) = (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 (M.op X0 X0))) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 (M.op X0 X0))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X0 (M.op X0 X0))) X0
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 (M.op X0 X0))) X0) = (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq738 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63 X0 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq63
    | (have j1 := eq64 X0 x
       grind)
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq748 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq765 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq748 (σ X0)
       grind)
    | exact superpose eq748 eq15
    | exact resolve eq15 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq765 X0
       have i₂ := eq748 X0
       grind)
    | exact superpose eq748 eq765
    | exact resolve eq765 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq765
  have eq2113 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
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
  have eq2138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2113 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2113
    | (have j0 := eq2113 X0 X1
       grind)
    | exact resolve eq2113 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq4015 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq12180 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4015
       have i₂ := eq2138 x y
       grind)
    | exact superpose eq2138 eq4015
    | (have j1 := eq2138 (σ x) (σ y)
       grind)
    | (have r₁ := eq4015
       have r₂ := eq2138 x y
       grind)
    | (have r₁ := eq4015
       have r₂ := eq2138 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4015
       have r₂ := eq2138 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4015 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12181 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq12180
  have eq12183 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12181
       grind)
    | exact superpose eq12181 eq16
    | exact resolve eq16 eq12181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12184 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12183
       have r₂ := eq784 x
       grind)
    | exact resolve eq12183 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12183
  have eq12185 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12184
       grind)
    | exact superpose eq12184 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12184
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12184
       grind)
    | exact resolve eq12 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12184
  have eq12186 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq12185
  have eq12187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4015
       have i₂ := eq12186
       grind)
    | exact superpose eq12186 eq4015
    | exact resolve eq4015 eq12186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4015 eq12186
  have eq12188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq12187
  have eq12189 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq12188
  have eq12192 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq12189
       grind)
    | exact superpose eq12189 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12189
       grind)
    | exact resolve eq12 eq12189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12189
  have eq12193 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12192
  have eq12196 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12193
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12193
    | exact resolve eq12193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq12209 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12196
       grind)
    | exact superpose eq12196 eq16
    | exact resolve eq16 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq12282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq12209
       have i₂ := eq2138 x y
       grind)
    | exact superpose eq2138 eq12209
    | (have j1 := eq2138 x y
       grind)
    | (have r₁ := eq12209
       have r₂ := eq2138 x y
       grind)
    | (have r₁ := eq12209
       have r₂ := eq2138 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq12209
       have r₂ := eq2138 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12209 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq12283 : x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq12282
  have eq12287 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12283
       grind)
    | exact superpose eq12283 eq16
    | exact resolve eq16 eq12283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12283
  have eq12288 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12287
       have r₂ := eq784 x
       grind)
    | exact resolve eq12287 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12287
  have eq12289 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq12288
       grind)
    | exact superpose eq12288 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12288
       grind)
    | exact resolve eq12 eq12288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12288
  have eq12290 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq12289
  have eq12291 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12209
       have i₂ := eq12290
       grind)
    | exact superpose eq12290 eq12209
    | exact resolve eq12209 eq12290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12209 eq12290
  have eq12295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq12291
  have eq12296 : (σ x) = (σ y) := by grind
  clear eq12295
  have eq12297 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12296
       grind)
    | exact superpose eq12296 eq16
    | exact resolve eq16 eq12296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12298 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12296
       grind)
    | exact superpose eq12296 eq10
    | exact resolve eq10 eq12296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12296
  have eq12359 : x = y := by
    first
    | (have i₁ := eq12298
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12298
    | exact resolve eq12298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12298
  have eq12360 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12297
       have i₂ := eq784 x
       grind)
    | exact superpose eq784 eq12297
    | exact resolve eq12297 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq12297
  have eq12366 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12360
       have i₂ := eq12359
       grind)
    | exact superpose eq12359 eq12360
    | exact resolve eq12360 eq12359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12359 eq12360
  have eq12367 : False := by grind
  exact eq12367

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
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
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq100
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq151 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq154 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq149
    | (have j0 := eq149 X0 X1
       grind)
    | exact resolve eq149 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq809 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154 x y
       grind)
    | exact superpose eq154 eq16
    | (have j1 := eq154 x y
       grind)
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq912 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq151
    | exact resolve eq151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq965 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq912 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq912
    | (have j0 := eq912 X0 X1
       grind)
    | exact resolve eq912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq4813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq809
       have i₂ := eq965 x y
       grind)
    | exact superpose eq965 eq809
    | (have j1 := eq965 x y
       grind)
    | (have r₁ := eq809
       have r₂ := eq965 x y
       grind)
    | (have r₁ := eq809
       have r₂ := eq965 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq809
       have r₂ := eq965 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq809 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq965
  have eq4814 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq4813
  have eq4816 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4814
       grind)
    | exact superpose eq4814 eq16
    | exact resolve eq16 eq4814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814
  have eq4817 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4816
       have r₂ := eq80 x
       grind)
    | exact resolve eq4816 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816
  have eq4825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4817
       grind)
    | exact superpose eq4817 eq103
    | exact resolve eq103 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq4835 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4825
       have r₂ := eq16
       grind)
    | exact resolve eq4825 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq4839 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4835
       grind)
    | exact superpose eq4835 eq10
    | exact resolve eq10 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq4890 : x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4839
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4839
    | exact resolve eq4839 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq4893 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4890
       grind)
    | exact superpose eq4890 eq16
    | exact resolve eq16 eq4890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4890
  have eq4894 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4893
       have r₂ := eq80 x
       grind)
    | exact resolve eq4893 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4893
  have eq4903 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4894
       grind)
    | exact superpose eq4894 eq10
    | exact resolve eq10 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4894
  have eq4954 : x = (M.op y y) := by
    first
    | (have i₁ := eq4903
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4903
    | exact resolve eq4903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4903
  have eq4970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq4954
       grind)
    | exact superpose eq4954 eq103
    | exact resolve eq103 eq4954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4954
  have eq4979 : False := by grind
  exact eq4979

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq261 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq261 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq261 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq261 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq263 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (k X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq9
    | exact resolve eq9 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq262 X1
       grind)
    | exact superpose eq262 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | (have r₁ := eq263 X0 X0
       have r₂ := eq262 X0
       grind)
    | exact resolve eq263 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 (σ X0) X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq262 X1
       grind)
    | exact superpose eq262 eq357
    | (have j0 := eq357 X0 X1
       grind)
    | exact resolve eq357 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq359 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq358
    | (have j0 := eq358 X0 X1
       grind)
    | exact resolve eq358 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq365 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq359 (σ x) (σ y)
       grind)
    | exact superpose eq359 eq16
    | (have j1 := eq359 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 (M.op X0 X0)))) = X0 ∨ (k X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq359 X0 (M.op X0 X0)
       grind)
    | exact superpose eq359 eq9
    | (have j1 := eq359 X0 (M.op X0 X0)
       grind)
    | exact resolve eq9 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 ∨ (k X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq387 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq365
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq365
    | exact resolve eq365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq394 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq262 X0
       grind)
    | exact superpose eq262 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq384
  have eq396 : (k (σ x) (σ x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq387
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq387
    | exact resolve eq387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq400 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k y y)) = (σ (k x x)) := by
    first
    | (have i₁ := eq396
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq396
    | exact resolve eq396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq401 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k y y)) = (σ (k x x)) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq400
       have i₂ := eq359 x y
       grind)
    | exact superpose eq359 eq400
    | (have j1 := eq359 y x
       grind)
    | exact resolve eq400 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq400
  have eq402 : (σ (k y y)) = (σ (k x x)) ∨ (k y y) = (k x x) := by grind
  clear eq401
  have eq405 : (k x x) = (τ (σ (k y y))) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq402
       grind)
    | exact superpose eq402 eq10
    | exact resolve eq10 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq439 : (k y y) = (k x x) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq405
       have i₂ := eq10 (k y y)
       grind)
    | exact superpose eq10 eq405
    | exact resolve eq405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq440 : (k y y) = (k x x) := by grind
  clear eq439
  have eq441 : ∀ X0 : G, x ≠ (k y y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq265 x X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq265
    | (have j0 := eq265 x X0
       grind)
    | exact resolve eq265 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ x) ≠ (σ (k y y)) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq275 x X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq275
    | (have j0 := eq275 x X0
       grind)
    | exact resolve eq275 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq488 : ∀ X0 X1 : G, (k X1 X1) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (σ X1) X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 (σ X0) X1
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (k X0 X0) ≠ (k y y) ∨ x = (k y y) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq270 x x
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq270
    | (have j0 := eq270 X0 y
       grind)
    | (have r₁ := eq270 y x
       have r₂ := eq440
       grind)
    | (have r₁ := eq270 x y
       have r₂ := eq440
       grind)
    | exact resolve eq270 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq527 : (M.op x y) = (k y x) ∨ x = (k y y) := by
    first
    | (have j0 := eq490 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq2162 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X1 (k X0 X0)) = (k X1 (k X0 X0)) ∨ (M.op X0 (M.op X2 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq265 (k X0 X0) X1
       have i₂ := eq394 X0 X2
       grind)
    | exact superpose eq394 eq265
    | (have j0 := eq265 (k X0 X0) X1
       have j1 := eq394 X0 X2
       grind)
    | (have r₁ := eq265 (k X0 X0) X1
       have r₂ := eq394 X0 X1
       grind)
    | exact resolve eq265 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq394
  have eq2175 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (k X1 (k X0 X0)) ∨ (M.op X0 (M.op X2 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2162 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq2780 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (k X0 (k X0 X0)))) = X0 ∨ (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq266 X0 X2
       have i₂ := eq2175 X0 X0 X1
       grind)
    | exact superpose eq2175 eq266
    | (have j1 := eq2175 X0 X1 X2
       grind)
    | exact resolve eq266 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq2175
  have eq2849 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2780 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780
  have eq2850 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 (k X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2849 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq2861 : ∀ X0 : G, x = (M.op x (M.op X0 (k x (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq2850 x X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq2850
    | exact resolve eq2850 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2863 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 (k (τ (σ X0)) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2850 (σ X0) X1
       have i₂ := eq20 (σ X0) X0 X0
       grind)
    | exact superpose eq20 eq2850
    | exact resolve eq2850 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2868 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (k X0 (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2863 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2863
    | exact resolve eq2863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2895 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (k x (k y y))))) := by
    intro X0
    first
    | (have i₁ := eq2868 x X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq2868
    | exact resolve eq2868 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq4274 : ∀ X0 : G, (k X0 X0) ≠ (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq488 x x
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq488
    | (have j0 := eq488 y X0
       grind)
    | exact resolve eq488 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq4564 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4274 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4274
    | (have j0 := eq4274 (σ X0)
       grind)
    | (have r₁ := eq4274 (σ y)
       have r₂ := eq15 y y
       grind)
    | exact resolve eq4274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4566 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq4564 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq4564
    | (have j0 := eq4564 X0
       grind)
    | exact resolve eq4564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564
  have eq9643 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have j0 := eq4566 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566
  have eq9709 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9643
       grind)
    | exact superpose eq9643 eq16
    | exact resolve eq16 eq9643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9643
  have eq9717 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9709
       have i₂ := eq527
       grind)
    | exact superpose eq527 eq9709
    | exact resolve eq9709 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq9709
  have eq9719 : (σ x) = (σ (k y y)) ∨ x = (k y y) := by grind
  clear eq9717
  have eq9750 : (k y y) = (τ (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq9719
       grind)
    | exact superpose eq9719 eq10
    | exact resolve eq10 eq9719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9719
  have eq9883 : x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9750
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9750
    | exact resolve eq9750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9750
  have eq9884 : x = (k y y) := by grind
  clear eq9883
  have eq9904 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq441
    | (have j0 := eq441 X0
       grind)
    | (have r₁ := eq441 X0
       have r₂ := eq9884
       grind)
    | exact resolve eq441 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq9909 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq446 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq446
    | (have j0 := eq446 X0
       grind)
    | exact resolve eq446 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq9921 : ∀ X0 : G, x = (M.op x (M.op X0 (k x x))) := by
    intro X0
    first
    | (have i₁ := eq2861 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq2861
    | exact resolve eq2861 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq9923 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (k x x)))) := by
    intro X0
    first
    | (have i₁ := eq2895 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq2895
    | exact resolve eq2895 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq9984 : ∀ X0 : G, y = (M.op y (M.op X0 (k y x))) := by
    intro X0
    first
    | (have i₁ := eq2850 y X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq2850
    | exact resolve eq2850 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850
  have eq10013 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq9909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9909
  have eq10014 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq9904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9904
  have eq10035 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ (k y y)))) := by
    intro X0
    first
    | (have i₁ := eq9923 X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq9923
    | exact resolve eq9923 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9923
  have eq10037 : ∀ X0 : G, x = (M.op x (M.op X0 (k y y))) := by
    intro X0
    first
    | (have i₁ := eq9921 X0
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq9921
    | exact resolve eq9921 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq9921
  have eq10066 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10035 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq10035
    | exact resolve eq10035 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10035
  have eq10068 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq10037 X0
       have i₂ := eq9884
       grind)
    | exact superpose eq9884 eq10037
    | exact resolve eq10037 eq9884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9884 eq10037
  have eq10391 : ∀ X0 : G, x = (M.op x (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq10068 X0
       have i₂ := eq10014 X0
       grind)
    | exact superpose eq10014 eq10068
    | exact resolve eq10068 eq10014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10068
  have eq10419 : y = (M.op y x) := by
    first
    | (have i₁ := eq9984 x
       have i₂ := eq10391 y
       grind)
    | exact superpose eq10391 eq9984
    | exact resolve eq9984 eq10391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9984
  have eq10424 : y = (k y x) := by
    first
    | (have i₁ := eq10419
       have i₂ := eq10014 y
       grind)
    | exact superpose eq10014 eq10419
    | exact resolve eq10419 eq10014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10014 eq10419
  have eq10426 : x = (M.op x y) := by
    first
    | (have i₁ := eq10391 y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq10391
    | exact resolve eq10391 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10391
  have eq10487 : ∀ X0 : G, (σ x) = (M.op (σ x) (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10066 X0
       have i₂ := eq10013 X0
       grind)
    | exact superpose eq10013 eq10066
    | exact resolve eq10066 eq10013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10013 eq10066
  have eq10514 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (k X0 x))) := by
    intro X0
    first
    | (have i₁ := eq10487 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq10487
    | exact resolve eq10487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10487
  have eq10596 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10514 y
       have i₂ := eq10424
       grind)
    | exact superpose eq10424 eq10514
    | exact resolve eq10514 eq10424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10424 eq10514
  have eq10628 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10596
       grind)
    | exact superpose eq10596 eq16
    | exact resolve eq16 eq10596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10596
  have eq10631 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq10628
       have i₂ := eq10426
       grind)
    | exact superpose eq10426 eq10628
    | exact resolve eq10628 eq10426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10426 eq10628
  have eq10632 : False := by grind
  exact eq10632

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       have j1 := eq117 X0 X1
       grind)
    | (have r₁ := eq132 X0 X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq132 X0 (σ (M.op X0 X0))
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq132 (M.op X0 X0) (σ X0)
       have r₂ := eq117 X0 X1
       grind)
    | exact resolve eq132 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq132
  have eq164 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq142 X1 (σ X0)
       grind)
    | exact superpose eq142 eq15
    | (have j1 := eq142 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq176 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq164 (τ X1) X0
       grind)
    | exact superpose eq164 eq19
    | (have j1 := eq164 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq164
  have eq258 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq176
    | exact resolve eq176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq258
    | (have j0 := eq258 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq885 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq897 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq885
       have i₂ := eq281 y x
       grind)
    | exact superpose eq281 eq885
    | (have j1 := eq281 (σ x) (σ y)
       grind)
    | (have r₁ := eq885
       have r₂ := eq281 y x
       grind)
    | (have r₁ := eq885
       have r₂ := eq281 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq885
       have r₂ := eq281 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq885 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq885
  have eq898 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq897
  have eq900 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq898
       grind)
    | exact superpose eq898 eq16
    | exact resolve eq16 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq901 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq900
       have r₂ := eq101 x
       grind)
    | exact resolve eq900 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq902 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq16
    | exact resolve eq16 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq901
       grind)
    | exact superpose eq901 eq10
    | exact resolve eq10 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq945 : x = y := by
    first
    | (have i₁ := eq903
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq903
    | exact resolve eq903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq946 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq902
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq902
    | exact resolve eq902 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq902
  have eq947 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq945
       grind)
    | exact superpose eq945 eq946
    | exact resolve eq946 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq946
  have eq948 : False := by grind
  exact eq948

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq64 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  clear eq49
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq68
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq87
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq91
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq65
  have eq575 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq8368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8368
    | exact resolve eq8368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8368
  have eq8380 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq8369
       have r₂ := eq28
       grind)
    | exact resolve eq8369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8384 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8380
    | exact resolve eq8380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8380
  have eq8394 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8384 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8384
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8384
       grind)
    | exact resolve eq12 eq8384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8384
  have eq12324 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq8394
    | (have j0 := eq8394 (σ x)
       grind)
    | (have r₁ := eq8394 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq8394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8394
  have eq12325 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12324
  have eq12326 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq12325
  have eq12335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq12326 eq73
    | exact resolve eq73 eq12326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq12326
  have eq12345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12335
  have eq12348 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12345
       have r₂ := eq28
       grind)
    | exact resolve eq12345 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12345
  have eq12351 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq12348
       grind)
    | exact superpose eq12348 eq92
    | exact resolve eq92 eq12348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12359 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq12348
       grind)
    | exact superpose eq12348 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12348
       grind)
    | exact resolve eq12 eq12348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12348
  have eq12369 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12351
    | exact resolve eq12351 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12351
  have eq18714 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12359 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12359
    | (have j0 := eq12359 x
       grind)
    | (have r₁ := eq12359 x
       have r₂ := eq19
       grind)
    | exact resolve eq12359 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12359
  have eq18715 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq18714
  have eq18716 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18715
  have eq18727 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq575 x y
       have i₂ := eq18716
       grind)
    | exact superpose eq18716 eq575
    | (have j0 := eq575 x y
       grind)
    | exact resolve eq575 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq18716
  have eq18731 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18727
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq18727
    | exact resolve eq18727 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18727
  have eq18741 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18731
    | exact resolve eq18731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18731
  have eq18744 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18741
       have r₂ := eq12369
       grind)
    | exact resolve eq18741 eq12369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18741
  have eq18745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18744
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq18744
    | exact resolve eq18744 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq18744
  have eq18746 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18745
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18745
    | exact resolve eq18745 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18745
  have eq18747 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18746
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18746
    | exact resolve eq18746 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746
  have eq18748 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18747
    | exact resolve eq18747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18747
  have eq18749 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18748
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18748
    | exact resolve eq18748 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18748
  have eq18750 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18749
    | exact resolve eq18749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18749
  have eq18751 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18750
  have eq18810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18751 eq12369
    | exact resolve eq12369 eq18751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369 eq18751
  have eq18850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18810
  have eq18858 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18850
       have r₂ := eq28
       grind)
    | exact resolve eq18850 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18850
  have eq18861 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18858 eq30
    | exact resolve eq30 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18858
  have eq18977 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18861
    | exact resolve eq18861 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18861
  have eq18978 : x = y := by grind
  clear eq18977
  have eq18998 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18978
       grind)
    | exact superpose eq18978 eq19
    | exact resolve eq19 eq18978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18999 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18978
       grind)
    | exact superpose eq18978 eq25
    | exact resolve eq25 eq18978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18978
  have eq19120 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18999
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18999
    | exact resolve eq18999 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18999
  have eq19139 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19120 eq27
    | exact resolve eq27 eq19120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19120
  have eq19324 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19139 eq64
    | exact resolve eq64 eq19139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq19139
  have eq19340 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19324
       have i₂ := eq18998
       grind)
    | exact superpose eq18998 eq19324
    | exact resolve eq19324 eq18998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18998 eq19324
  have eq19353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19340 eq15
    | exact resolve eq15 eq19340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19340
  have eq19430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19353
    | exact resolve eq19353 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19353
  have eq19451 : False := by grind
  exact eq19451

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq459 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
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
  have eq462 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq2982 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq462
    | exact resolve eq462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3025 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2982 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2982
    | (have j0 := eq2982 X0 X1
       grind)
    | exact resolve eq2982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq3035 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq3025 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3025 X0 X1
       grind)
    | exact superpose eq3025 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq3025 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3025 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3025 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3025 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3068 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq3025 X1 (τ X0)
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq3025 (τ X0) (τ X0)
       grind)
    | exact superpose eq3025 eq30
    | (have j1 := eq3025 X1 (τ X0)
       grind)
    | exact resolve eq30 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3025
  have eq3075 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3076 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3078 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3068 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq3068
    | (have j0 := eq3068 X0 X1
       grind)
    | exact resolve eq3068 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3068
  have eq3167 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq3076 X0 X1
       grind)
    | exact superpose eq3076 eq10
    | (have j1 := eq3076 X0 X1
       grind)
    | exact resolve eq10 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076
  have eq3211 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3167 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3167
    | (have j0 := eq3167 X0 X1
       grind)
    | exact resolve eq3167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3243 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3211 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3211
    | (have j0 := eq3211 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq3243
    | (have j0 := eq3243 X0 X1
       grind)
    | exact resolve eq3243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3545 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq459 (σ x) y
       grind)
    | exact superpose eq459 eq16
    | (have j1 := eq459 (σ x) y
       grind)
    | (have r₁ := eq16
       have r₂ := eq459 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3558 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3545
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq3545
    | exact resolve eq3545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq3569 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3558
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3558
    | exact resolve eq3558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq8644 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3078 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3078
    | exact resolve eq3078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078
  have eq8782 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8644 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8644
    | (have j0 := eq8644 X0 X1
       grind)
    | exact resolve eq8644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8805 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8782 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq8782
    | (have j0 := eq8782 X0 X1
       grind)
    | exact resolve eq8782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8782
  have eq19482 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3401 y x
       grind)
    | exact superpose eq3401 eq16
    | (have j1 := eq3401 y x
       grind)
    | exact resolve eq16 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq19588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq19482
       have i₂ := eq8805 x y
       grind)
    | exact superpose eq8805 eq19482
    | (have j1 := eq8805 x y
       grind)
    | (have r₁ := eq19482
       have r₂ := eq8805 x y
       grind)
    | (have r₁ := eq19482
       have r₂ := eq8805 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq19482
       have r₂ := eq8805 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq19482 eq8805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8805 eq19482
  have eq19591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19588
  have eq19592 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq19591
  have eq19597 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19592
       grind)
    | exact superpose eq19592 eq16
    | exact resolve eq16 eq19592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19592
  have eq19598 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19597
       have r₂ := eq22 x
       grind)
    | exact resolve eq19597 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19597
  have eq19600 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19598
       grind)
    | exact superpose eq19598 eq10
    | exact resolve eq10 eq19598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19598
  have eq19675 : x = y ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq19600
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19600
    | exact resolve eq19600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19600
  have eq19677 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19675
       grind)
    | exact superpose eq19675 eq16
    | exact resolve eq16 eq19675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19675
  have eq19678 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq19677
       have r₂ := eq22 x
       grind)
    | exact resolve eq19677 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677
  have eq19679 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3569
       have i₂ := eq19678
       grind)
    | exact superpose eq19678 eq3569
    | (have r₁ := eq3569
       have r₂ := eq19678
       grind)
    | exact resolve eq3569 eq19678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq19680 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq19678
       grind)
    | exact superpose eq19678 eq10
    | exact resolve eq10 eq19678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19734 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq19679
  have eq19756 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19680
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq19680
    | exact resolve eq19680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19680
  have eq19760 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19756
       grind)
    | exact superpose eq19756 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19756
       grind)
    | exact resolve eq13 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19756
  have eq19761 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq19760
  have eq19763 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19761
       grind)
    | exact superpose eq19761 eq16
    | exact resolve eq16 eq19761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19761
  have eq19764 : (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq19763
       have r₂ := eq22 x
       grind)
    | exact resolve eq19763 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19763
  have eq20675 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19734
       grind)
    | exact superpose eq19734 eq16
    | exact resolve eq16 eq19734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19734
  have eq20781 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20675
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20675
    | exact resolve eq20675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20675
  have eq20804 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq20781
       have r₂ := eq19678
       grind)
    | exact resolve eq20781 eq19678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20781
  have eq20805 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq20804
       have i₂ := eq19764
       grind)
    | exact superpose eq19764 eq20804
    | exact resolve eq20804 eq19764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19764 eq20804
  have eq20824 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq20805
       grind)
    | exact superpose eq20805 eq11
    | exact resolve eq11 eq20805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20805
  have eq20948 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20824
       grind)
    | exact superpose eq20824 eq16
    | exact resolve eq16 eq20824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20824
  have eq20968 : False := by grind
  exact eq20968
