import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation860 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq302 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq305 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq303 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq303 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq303 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq317 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq305 (σ X0)
       grind)
    | exact superpose eq305 eq15
    | exact resolve eq15 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq317
    | exact resolve eq317 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq317
  have eq385 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       have j1 := eq386 X0 X1
       grind)
    | (have r₁ := eq385 X0 X1
       have r₂ := eq386 X0 X1
       grind)
    | exact resolve eq385 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq554 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq387 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq387 X1 (σ X0)
       grind)
    | exact superpose eq387 eq15
    | (have j1 := eq387 X1 (σ X0)
       grind)
    | exact resolve eq15 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq594 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq554 (τ X1) X0
       grind)
    | exact superpose eq554 eq18
    | (have j1 := eq554 (τ X1) X0
       grind)
    | exact resolve eq18 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq554
  have eq872 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq594
    | exact resolve eq594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq922 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq872
    | (have j0 := eq872 X0 X1
       grind)
    | exact resolve eq872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1986 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq565 x y
       grind)
    | exact superpose eq565 eq16
    | (have j1 := eq565 x y
       grind)
    | exact resolve eq16 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2026 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq2208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1986
       have i₂ := eq922 y x
       grind)
    | exact superpose eq922 eq1986
    | (have j1 := eq922 (σ y) (σ x)
       grind)
    | (have r₁ := eq1986
       have r₂ := eq922 y x
       grind)
    | exact resolve eq1986 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2209 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2208
  have eq2214 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2209
       grind)
    | exact superpose eq2209 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2209
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2209
       grind)
    | exact resolve eq13 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2220 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2214
  have eq3755 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2026 x y
       have i₂ := eq2220
       grind)
    | exact superpose eq2220 eq2026
    | (have j0 := eq2026 x y
       grind)
    | exact resolve eq2026 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026 eq2220
  have eq3764 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3755
  have eq3765 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3764
  have eq3771 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3765
       grind)
    | exact superpose eq3765 eq16
    | exact resolve eq16 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3778 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3765
       grind)
    | exact superpose eq3765 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3765
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq3765
       grind)
    | exact resolve eq13 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3765
  have eq3787 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3778
  have eq3789 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3787
       have i₂ := eq336 y
       grind)
    | exact superpose eq336 eq3787
    | exact resolve eq3787 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq3787
  have eq3791 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3789
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3789
    | exact resolve eq3789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq6348 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq922 y x
       have i₂ := eq3791
       grind)
    | exact superpose eq3791 eq922
    | (have j0 := eq922 y x
       grind)
    | exact resolve eq922 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq6411 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq6348
       have r₂ := eq3771
       grind)
    | exact resolve eq6348 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6445 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3771
       have i₂ := eq6411
       grind)
    | exact superpose eq6411 eq3771
    | exact resolve eq3771 eq6411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411
  have eq6470 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq6445
  have eq6471 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq6470
  have eq6478 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq386 y X0
       have i₂ := eq6471
       grind)
    | exact superpose eq6471 eq386
    | (have j0 := eq386 y X0
       grind)
    | (have r₁ := eq386 y x
       have r₂ := eq6471
       grind)
    | exact resolve eq386 eq6471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6471
  have eq6520 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq6478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq6523 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq6520 X0
       have j1 := eq386 y X0
       grind)
    | (have r₁ := eq6520 X0
       have r₂ := eq386 y x
       grind)
    | exact resolve eq6520 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq6520
  have eq6543 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq6523 (σ X0)
       grind)
    | exact superpose eq6523 eq15
    | exact resolve eq15 eq6523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6523
  have eq6702 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6543 x
       grind)
    | exact superpose eq6543 eq16
    | exact resolve eq16 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543
  have eq6862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6702
       have i₂ := eq922 y x
       grind)
    | exact superpose eq922 eq6702
    | (have j1 := eq922 y x
       grind)
    | (have r₁ := eq6702
       have r₂ := eq922 y x
       grind)
    | exact resolve eq6702 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq6863 : x = (M.op x y) := by grind
  clear eq6862
  have eq6867 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3771
       have i₂ := eq6863
       grind)
    | exact superpose eq6863 eq3771
    | exact resolve eq3771 eq6863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771 eq6863
  have eq6890 : y = (M.op y y) := by grind
  clear eq6867
  have eq6896 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq6890
       grind)
    | exact superpose eq6890 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq6890
       grind)
    | exact resolve eq12 eq6890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq6945 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq6896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6995 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq6702
       have i₂ := eq6945 x
       grind)
    | exact superpose eq6945 eq6702
    | exact resolve eq6702 eq6945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702 eq6945
  have eq7001 : False := by grind
  exact eq7001

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq999 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq999
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq999
    | exact resolve eq999 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1019 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq998
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq998
    | exact resolve eq998 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1049 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16480 : (M.op x y) ≠ (k y y) ∨ x = y ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq1049 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1049
    | (have j0 := eq1049 y x
       grind)
    | exact resolve eq1049 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16481 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1049
    | (have j0 := eq1049 (σ y) (σ x)
       grind)
    | exact resolve eq1049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq16489 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16480
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq16480
    | (have r₁ := eq16480
       have r₂ := eq1019
       grind)
    | exact resolve eq16480 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq16480
  have eq16490 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq16489
  have eq16491 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq16490
  have eq16497 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16491
       grind)
    | exact superpose eq16491 eq40
    | exact resolve eq40 eq16491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16491
  have eq16499 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16497
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16497
    | exact resolve eq16497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16497
  have eq16503 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq16499
    | exact resolve eq16499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16499
  have eq16635 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1018 eq16481
    | (have r₁ := eq16481
       have r₂ := eq1018
       grind)
    | exact resolve eq16481 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq16481
  have eq16636 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq16635
  have eq16637 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16636
  have eq16644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16637 eq16503
    | exact resolve eq16503 eq16637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16503 eq16637
  have eq16649 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16644
       have r₂ := eq27
       grind)
    | exact resolve eq16644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16652 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16649 eq31
    | exact resolve eq31 eq16649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16649
  have eq16753 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16652
    | exact resolve eq16652 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16652
  have eq16754 : x = y := by grind
  clear eq16753
  have eq17070 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16754
       grind)
    | exact superpose eq16754 eq18
    | exact resolve eq18 eq16754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17071 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16754
       grind)
    | exact superpose eq16754 eq24
    | exact resolve eq24 eq16754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16754
  have eq17107 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17071
    | exact resolve eq17071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17071
  have eq17108 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq17070
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq17070
    | exact resolve eq17070 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17070
  have eq17109 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17107 eq26
    | exact resolve eq26 eq17107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17107
  have eq17207 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17109
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq17109
    | exact resolve eq17109 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq17109
  have eq17211 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17108
       grind)
    | exact superpose eq17108 eq39
    | exact resolve eq39 eq17108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq17108
  have eq17234 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17211
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17211
    | exact resolve eq17211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17211
  have eq17243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17207 eq17234
    | exact resolve eq17234 eq17207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207 eq17234
  have eq17250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17243
    | exact resolve eq17243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq17243
  have eq17254 : False := by grind
  exact eq17254

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq388 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq420 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq388
    | (have j0 := eq388 X0 X1
       grind)
    | exact resolve eq388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq388
  have eq425 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq420 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq420 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq428 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq425
  have eq668 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq675 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq428 (σ X0) X1
       grind)
    | exact superpose eq428 eq15
    | (have j1 := eq428 (σ X0) X1
       grind)
    | exact resolve eq15 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq699 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq732 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq668 (τ X1) X0
       grind)
    | exact superpose eq668 eq17
    | (have j1 := eq668 (τ X1) X0
       grind)
    | exact resolve eq17 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq668
  have eq961 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq732
    | exact resolve eq732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq1006 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq961 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq961
    | (have j0 := eq961 X0 X1
       grind)
    | exact resolve eq961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq3761 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq699 x y
       grind)
    | exact superpose eq699 eq16
    | (have j1 := eq699 x y
       grind)
    | exact resolve eq16 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3798 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq3892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3761
       have i₂ := eq1006 y x
       grind)
    | exact superpose eq1006 eq3761
    | (have j1 := eq1006 y x
       grind)
    | (have r₁ := eq3761
       have r₂ := eq1006 y x
       grind)
    | exact resolve eq3761 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761
  have eq3893 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3892
  have eq3898 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3893
       grind)
    | exact superpose eq3893 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3899 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3893
       grind)
    | exact superpose eq3893 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3893
       grind)
    | exact resolve eq13 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3916 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3899
  have eq3917 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3898
       have r₂ := eq3916
       grind)
    | exact resolve eq3898 eq3916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898 eq3916
  have eq3983 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq412 x y
       have i₂ := eq3917
       grind)
    | exact superpose eq3917 eq412
    | (have j0 := eq412 x y
       grind)
    | exact resolve eq412 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq3993 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3983
  have eq3994 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3993
  have eq4008 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3994
       grind)
    | exact superpose eq3994 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3994
       grind)
    | exact resolve eq12 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994
  have eq4028 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4008
  have eq4031 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq4028
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4028
    | exact resolve eq4028 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq4466 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4031
       grind)
    | exact superpose eq4031 eq12
    | exact resolve eq12 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4467 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4031
       grind)
    | exact superpose eq4031 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4488 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq4467
       have r₂ := eq67 x
       grind)
    | exact resolve eq4467 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4489 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq4466
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4466
    | exact resolve eq4466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4492 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq4488
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4488
    | exact resolve eq4488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4488
  have eq4493 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq4492
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq4492
    | exact resolve eq4492 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4494 : (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4493
       have r₂ := eq4489
       grind)
    | exact resolve eq4493 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489 eq4493
  have eq4662 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq4494
  have eq4928 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3798 x y
       have i₂ := eq3917
       grind)
    | exact superpose eq3917 eq3798
    | (have j0 := eq3798 x y
       grind)
    | exact resolve eq3798 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3798 eq3917
  have eq4959 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4928
  have eq4960 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4959
  have eq5126 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4960
       grind)
    | exact superpose eq4960 eq16
    | exact resolve eq16 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5131 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4960
       grind)
    | exact superpose eq4960 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4960
  have eq5158 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5131
       have r₂ := eq67 x
       grind)
    | exact resolve eq5131 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5131
  have eq5162 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5158
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5158
    | exact resolve eq5158 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq5163 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5162
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq5162
    | exact resolve eq5162 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq5162
  have eq5164 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5163
       have r₂ := eq4662
       grind)
    | exact resolve eq5163 eq4662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662 eq5163
  have eq5271 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1006 y x
       have i₂ := eq5164
       grind)
    | exact superpose eq5164 eq1006
    | (have j0 := eq1006 y x
       grind)
    | exact resolve eq1006 eq5164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq5164
  have eq5333 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq5271
       have r₂ := eq5126
       grind)
    | exact resolve eq5271 eq5126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5457 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5126
       have i₂ := eq5333
       grind)
    | exact superpose eq5333 eq5126
    | exact resolve eq5126 eq5333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126 eq5333
  have eq5494 : False := by grind
  exact eq5494

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq104 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq143 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq532 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq143
    | exact resolve eq143 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq533 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq532
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq532
    | exact resolve eq532 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq533
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq533
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq533 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq533
  have eq569 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq568
  have eq2879 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq569
       grind)
    | exact superpose eq569 eq10
    | exact resolve eq10 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq2924 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2879
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2879
    | exact resolve eq2879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq2925 : (M.op x x) = (M.op y y) := by grind
  clear eq2924
  have eq2941 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq104 X0 y
       have i₂ := eq2925
       grind)
    | exact superpose eq2925 eq104
    | exact resolve eq104 eq2925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq2984 : x = y := by
    first
    | (have i₁ := eq2941 x
       have i₂ := eq104 x x
       grind)
    | exact superpose eq104 eq2941
    | exact resolve eq2941 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq2941
  have eq3046 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2984
       grind)
    | exact superpose eq2984 eq16
    | exact resolve eq16 eq2984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq3047 : False := by grind
  exact eq3047

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq50 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq100 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq100 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq100 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq101 (σ X0)
       grind)
    | exact superpose eq101 eq10
    | exact resolve eq10 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq103
    | exact resolve eq103 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq101 sF3
       grind)
    | exact superpose eq101 eq86
    | exact resolve eq86 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq111 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq101 y
       grind)
    | exact superpose eq101 eq110
    | exact resolve eq110 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq110
  have eq138 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq388 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq395 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq397 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq401
    | exact resolve eq401 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq409 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq395
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq395
    | exact resolve eq395 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq411 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq392
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq392
    | exact resolve eq392 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq414 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq388
    | exact resolve eq388 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq404 X0 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq404
    | exact resolve eq404 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq420 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq414
    | exact resolve eq414 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X1 (σ X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq397
    | exact resolve eq397 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq397 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq397 (M.op X0 X0) X0
       grind)
    | exact superpose eq397 eq397
    | exact resolve eq397 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq409 eq52
    | exact resolve eq52 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq886 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq881
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq881
    | exact resolve eq881 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq888 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq886
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq886
    | exact resolve eq886 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq889 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq888
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq888
    | exact resolve eq888 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq890 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq889 eq397
    | exact resolve eq397 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq910 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq411 eq52
    | exact resolve eq52 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq915 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq910
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq910
    | exact resolve eq910 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq917 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq915
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq915
    | exact resolve eq915 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq918 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq917
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq917
    | exact resolve eq917 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq919 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq397 y y
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq397
    | exact resolve eq397 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq2980 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq415 (σ X0) (σ X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq415
    | exact resolve eq415 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq3039 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2980 X0
       have i₂ := eq422 X0 (σ X0)
       grind)
    | exact superpose eq422 eq2980
    | exact resolve eq2980 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq2980
  have eq3239 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq52
    | exact resolve eq52 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq3243 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3239 X0 X1
       have i₂ := eq52 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq3239
    | exact resolve eq3239 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3291 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq3243
    | exact resolve eq3243 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3329 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3291 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq3291
    | exact resolve eq3291 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3291
  have eq3353 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3329 X0 X1
       have i₂ := eq415 X1 X0
       grind)
    | exact superpose eq415 eq3329
    | exact resolve eq3329 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq3329
  have eq3515 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3353 X1 X2
       have i₂ := eq3353 X1 X0
       grind)
    | (have i₁ := eq3353 X0 X1
       have i₂ := eq3353 X0 X0
       grind)
    | exact superpose eq3353 eq3353
    | exact resolve eq3353 eq3353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq3782 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq919 eq3515
    | exact resolve eq3515 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq3791 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq890 eq3515
    | exact resolve eq3515 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq3515
  have eq10297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10297
    | exact resolve eq10297 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10297
  have eq10307 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10298
       have r₂ := eq27
       grind)
    | exact resolve eq10298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10298
  have eq10310 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10307
    | exact resolve eq10307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10307
  have eq10312 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10310
    | exact resolve eq10310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10310
  have eq10315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10312 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10312
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10312
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10312
       grind)
    | exact resolve eq12 eq10312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10312
  have eq10329 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10315
       have r₂ := eq26
       grind)
    | exact resolve eq10315 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10315
  have eq10331 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10329
    | exact resolve eq10329 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10329
  have eq10332 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq10331
  have eq10339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10332 eq99
    | exact resolve eq99 eq10332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq10332
  have eq10345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10339
  have eq10347 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10345
       have r₂ := eq27
       grind)
    | exact resolve eq10345 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10345
  have eq10461 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10347
       grind)
    | exact superpose eq10347 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10347
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10347
       grind)
    | exact resolve eq12 eq10347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10347
  have eq10475 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10461
       have r₂ := eq18
       grind)
    | exact resolve eq10461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461
  have eq10477 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10475
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10475
    | exact resolve eq10475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10475
  have eq10478 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10477
  have eq10481 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq10478
       grind)
    | exact superpose eq10478 eq85
    | exact resolve eq85 eq10478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq10478
  have eq10495 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10481
    | exact resolve eq10481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481
  have eq10613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10495 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10613
    | exact resolve eq10613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq10625 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10616
       have r₂ := eq27
       grind)
    | exact resolve eq10616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10616
  have eq10628 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10625
    | exact resolve eq10625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10625
  have eq10630 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10628
    | exact resolve eq10628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10628
  have eq10631 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10630
  have eq10635 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10631 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10631
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10631
       grind)
    | exact resolve eq12 eq10631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10631
  have eq10649 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10635
       have r₂ := eq26
       grind)
    | exact resolve eq10635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635
  have eq10651 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10649
    | exact resolve eq10649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10649
  have eq10652 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10651
  have eq10785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10652 eq10495
    | exact resolve eq10495 eq10652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10495 eq10652
  have eq10787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10785
  have eq10791 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10787
       have r₂ := eq27
       grind)
    | exact resolve eq10787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787
  have eq10808 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10791 eq3791
    | exact resolve eq3791 eq10791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791 eq10791
  have eq10810 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10808 x
       have i₂ := eq397 x sF2
       grind)
    | exact superpose eq397 eq10808
    | exact resolve eq10808 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10808
  have eq10925 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10810 eq138
    | exact resolve eq138 eq10810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq10810
  have eq10979 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10925
    | exact resolve eq10925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10925
  have eq11258 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423 y
       have i₂ := eq10979
       grind)
    | exact superpose eq10979 eq423
    | exact resolve eq423 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq10979
  have eq11292 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11258
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11258
    | exact resolve eq11258 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq11258
  have eq11293 : x = (M.op x y) := by grind
  clear eq11292
  have eq11306 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11293 eq20
    | exact resolve eq20 eq11293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11369 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq11293 eq3782
    | exact resolve eq3782 eq11293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782 eq11293
  have eq11371 : x = (M.op y y) := by
    first
    | (have i₁ := eq11369 x
       have i₂ := eq397 x x
       grind)
    | exact superpose eq397 eq11369
    | exact resolve eq11369 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq11369
  have eq11423 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11306
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11306
    | exact resolve eq11306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11306
  have eq11616 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3039 y
       have i₂ := eq11371
       grind)
    | exact superpose eq11371 eq3039
    | exact resolve eq3039 eq11371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039 eq11371
  have eq11644 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11616
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11616
    | exact resolve eq11616 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11616
  have eq11662 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11644
    | exact resolve eq11644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11644
  have eq11670 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11662
    | exact resolve eq11662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11662
  have eq11676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11423 eq11670
    | exact resolve eq11670 eq11423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11423 eq11670
  have eq11679 : False := by grind
  exact eq11679

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyy_pyx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq47 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq65 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq65
    | exact resolve eq65 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq138 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq171 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
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
  have eq281 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 (σ X0)
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq78 y
       grind)
    | exact superpose eq78 eq89
    | (have j1 := eq78 y
       grind)
    | exact resolve eq89 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq302 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq48 eq49
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq49 (M.op X1 X1) X0
       grind)
    | exact superpose eq49 eq308
    | exact resolve eq308 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq312 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq302
       have i₂ := eq49 sF4 sF4
       grind)
    | exact superpose eq49 eq302
    | exact resolve eq302 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq314 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq299
       have i₂ := eq49 sF0 sF0
       grind)
    | exact superpose eq49 eq299
    | exact resolve eq299 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq49 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq49 eq296
    | exact resolve eq296 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq317 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq49 X1 X1
       grind)
    | exact superpose eq49 eq310
    | exact resolve eq310 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq321 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq316
    | exact resolve eq316 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq304 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq304 (M.op X0 X0) X0
       grind)
    | exact superpose eq304 eq304
    | exact resolve eq304 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq312 eq49
    | exact resolve eq49 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq573 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq569
       have i₂ := eq49 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq49 eq569
    | exact resolve eq569 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq574 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq573
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq573
    | exact resolve eq573 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq575 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq574
       have i₂ := eq49 sF3 sF3
       grind)
    | exact superpose eq49 eq574
    | exact resolve eq574 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq576 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq575 eq304
    | exact resolve eq304 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq314 eq49
    | exact resolve eq49 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq650 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq646
       have i₂ := eq49 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq49 eq646
    | exact resolve eq646 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq651 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq650
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq650
    | exact resolve eq650 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq652 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq651
       have i₂ := eq49 y y
       grind)
    | exact superpose eq49 eq651
    | exact resolve eq651 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq653 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq304 y y
       have i₂ := eq652
       grind)
    | exact superpose eq652 eq304
    | exact resolve eq304 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq3153 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq321 X0 X1
       grind)
    | exact superpose eq321 eq49
    | exact resolve eq49 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq3159 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3153 X0 X1
       have i₂ := eq49 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq49 eq3153
    | exact resolve eq3153 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3198 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3159 X0 X1
       have i₂ := eq49 (M.op X0 X0) X1
       grind)
    | exact superpose eq49 eq3159
    | exact resolve eq3159 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq3229 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3198 X0 X1
       have i₂ := eq49 X0 X0
       grind)
    | exact superpose eq49 eq3198
    | exact resolve eq3198 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3198
  have eq3248 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3229 X0 X1
       have i₂ := eq317 X1 X0
       grind)
    | exact superpose eq317 eq3229
    | exact resolve eq3229 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3730 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq3776 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3248 X1 X2
       have i₂ := eq3248 X1 X0
       grind)
    | (have i₁ := eq3248 X0 X1
       have i₂ := eq3248 X0 X0
       grind)
    | exact superpose eq3248 eq3248
    | exact resolve eq3248 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq4871 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) (M.op (σ X0) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq171 eq317
    | (have j1 := eq171 X0
       grind)
    | exact resolve eq317 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq317
  have eq4880 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ (k X0 y)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq575 eq4871
    | (have j0 := eq4871 X0
       grind)
    | exact resolve eq4871 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq4871
  have eq4975 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq653 eq3776
    | exact resolve eq3776 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq4984 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq576 eq3776
    | exact resolve eq3776 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq3776
  have eq25892 : y = (M.op y (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq66
       grind)
    | exact superpose eq66 eq14
    | exact resolve eq14 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq25939 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25892
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq25892
    | exact resolve eq25892 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25892
  have eq25981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq25939 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq25939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq25981
    | exact resolve eq25981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq25993 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25982
       have r₂ := eq28
       grind)
    | exact resolve eq25982 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25982
  have eq26027 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq25993 eq14
    | exact resolve eq14 eq25993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25993
  have eq26074 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26027
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq26027
    | exact resolve eq26027 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26027
  have eq26120 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq26074 eq323
    | exact resolve eq323 eq26074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26074
  have eq26175 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq26120
    | exact resolve eq26120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26120
  have eq26200 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq323 y
       have i₂ := eq26175
       grind)
    | exact superpose eq26175 eq323
    | exact resolve eq323 eq26175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26175
  have eq26254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26200
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26200
    | exact resolve eq26200 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26200
  have eq26260 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26254 eq28
    | exact resolve eq28 eq26254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26276 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26254 eq4984
    | exact resolve eq4984 eq26254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26254
  have eq26277 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26276 x
       have i₂ := eq304 x sF2
       grind)
    | exact superpose eq304 eq26276
    | exact resolve eq26276 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26276
  have eq27375 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26277
  have eq27659 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27375 eq25939
    | exact resolve eq25939 eq27375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25939 eq27375
  have eq27661 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27659
  have eq27663 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27661
       have r₂ := eq26260
       grind)
    | exact resolve eq27661 eq26260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260 eq27661
  have eq27836 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq323 y
       have i₂ := eq27663
       grind)
    | exact superpose eq27663 eq323
    | exact resolve eq323 eq27663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27663
  have eq27894 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27836
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27836
    | exact resolve eq27836 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27836
  have eq27895 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq27894
  have eq27903 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27895 eq30
    | exact resolve eq30 eq27895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq27895
  have eq28040 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq27903
    | exact resolve eq27903 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27903
  have eq28041 : x = (M.op x y) ∨ x = y := by grind
  clear eq28040
  have eq28205 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28041 eq21
    | exact resolve eq21 eq28041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28281 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28041 eq4975
    | exact resolve eq4975 eq28041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4975 eq28041
  have eq28282 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq28281 x
       have i₂ := eq304 x x
       grind)
    | exact superpose eq304 eq28281
    | exact resolve eq28281 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq28281
  have eq28345 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq28205
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28205
    | exact resolve eq28205 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28205
  have eq28503 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq286
       have i₂ := eq28282
       grind)
    | exact superpose eq28282 eq286
    | exact resolve eq286 eq28282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq28282
  have eq28563 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq28503
  have eq28582 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq28563
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28563
    | exact resolve eq28563 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28563
  have eq29234 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq28582
       have i₂ := eq78 sF3
       grind)
    | exact superpose eq78 eq28582
    | (have j1 := eq78 (σ y)
       grind)
    | exact resolve eq28582 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq235252 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq235309 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq29234
  have eq243410 : (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq235252 eq28582
    | exact resolve eq28582 eq235252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28582 eq235252
  have eq243472 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq243410
  have eq243485 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq243472
       have r₂ := eq235309
       grind)
    | exact resolve eq243472 eq235309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235309 eq243472
  have eq244002 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq243485 eq323
    | exact resolve eq323 eq243485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq243485
  have eq244081 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq244002
    | exact resolve eq244002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244002
  have eq244089 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq244081 eq28
    | exact resolve eq28 eq244081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244081
  have eq244145 : x = y := by
    first
    | (have r₁ := eq244089
       have r₂ := eq28345
       grind)
    | exact resolve eq244089 eq28345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28345 eq244089
  have eq244146 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq244145
       grind)
    | exact superpose eq244145 eq19
    | exact resolve eq19 eq244145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq244147 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq244145
       grind)
    | exact superpose eq244145 eq25
    | exact resolve eq25 eq244145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq244466 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq244147
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq244147
    | exact resolve eq244147 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244147
  have eq245710 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq244466 eq27
    | exact resolve eq27 eq244466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq246078 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq244146
  have eq246245 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq246078 eq97
    | exact resolve eq97 eq246078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246287 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq246245
    | exact resolve eq246245 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246245
  have eq259521 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4880 X0
       have i₂ := eq244145
       grind)
    | exact superpose eq244145 eq4880
    | (have j0 := eq4880 X0
       grind)
    | exact resolve eq4880 eq244145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4880 eq244145
  have eq259522 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq244466 eq259521
    | (have j0 := eq259521 X0
       grind)
    | exact resolve eq259521 eq244466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259521
  have eq259523 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq245710 eq259522
    | (have j0 := eq259522 X0
       grind)
    | exact resolve eq259522 eq245710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259522
  have eq259524 : ∀ X0 : G, (σ X0) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq244466 eq259523
    | (have j0 := eq259523 X0
       grind)
    | exact resolve eq259523 eq244466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259523
  have eq259525 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq245710 eq259524
    | (have j0 := eq259524 X0
       grind)
    | exact resolve eq259524 eq245710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259524
  have eq260184 : (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq259525
    | (have j0 := eq259525 (M.op x y)
       grind)
    | exact resolve eq259525 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq259525
  have eq260266 : (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq260184
       have r₂ := eq28
       grind)
    | exact resolve eq260184 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260184
  have eq260510 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq97 eq260266
    | exact resolve eq260266 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq260266
  have eq260738 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq246287 eq260510
    | exact resolve eq260510 eq246287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246287 eq260510
  have eq260963 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq4984 eq260738
    | exact resolve eq260738 eq4984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4984 eq260738
  have eq261151 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq244466 eq260963
    | exact resolve eq260963 eq244466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260963
  have eq261219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq245710 eq261151
    | exact resolve eq261151 eq245710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261151
  have eq261262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq261219
       have r₂ := eq28
       grind)
    | exact resolve eq261219 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261219
  have eq261414 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq261262 eq14
    | exact resolve eq14 eq261262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261262
  have eq261448 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48 eq261414
    | exact resolve eq261414 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq261414
  have eq261451 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq244466 eq261448
    | exact resolve eq261448 eq244466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244466 eq261448
  have eq261455 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq261451 eq29
    | exact resolve eq29 eq261451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq261477 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq261451 eq138
    | exact resolve eq138 eq261451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq261726 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq153 eq261477
    | exact resolve eq261477 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq261477
  have eq261747 : x = (M.op x y) := by
    first
    | exact superpose eq31 eq261455
    | exact resolve eq261455 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq261455
  have eq261795 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq246078 eq261726
    | exact resolve eq261726 eq246078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246078 eq261726
  have eq267340 : x = (k x x) := by
    first
    | exact superpose eq261747 eq261795
    | exact resolve eq261795 eq261747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261747 eq261795
  have eq267546 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3730 x
       have i₂ := eq267340
       grind)
    | exact superpose eq267340 eq3730
    | (have j0 := eq3730 x
       grind)
    | exact resolve eq3730 eq267340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730 eq267340
  have eq267552 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq267546
  have eq267558 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq267552
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq267552
    | exact resolve eq267552 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq267552
  have eq267585 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq245710 eq267558
    | exact resolve eq267558 eq245710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245710 eq267558
  have eq267610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq261451 eq267585
    | exact resolve eq267585 eq261451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261451 eq267585
  have eq267635 : False := by grind
  exact eq267635

/-- `Equation934`: `x = y ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxy_pyx_Equation934 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law934 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law934.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X1 X2) (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X3 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) (M.op X0 X1)) X3 X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq65 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq65 X0 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq65
    | exact resolve eq65 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq91 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq60 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq84
    | exact resolve eq84 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq84
  have eq219 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X0 (M.op (M.op X0 (M.op X1 X0)) X2)
       have i₂ := eq9 X2 (M.op X1 X0) (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq246 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219 (M.op X0 X1) (M.op (M.op X0 X1) X0) X2
       have i₂ := eq9 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq9 eq219
    | exact resolve eq219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq304 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X2 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) X0
       have i₂ := eq246 X0 X2 (M.op X0 X1)
       grind)
    | exact superpose eq246 eq9
    | exact resolve eq9 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op (M.op X2 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq304 X2 (M.op (M.op X2 X3) (M.op X3 X1)) X0
       have i₂ := eq9 X1 X2 X3
       grind)
    | exact superpose eq9 eq304
    | exact resolve eq304 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq304
    | exact resolve eq304 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X1 X0) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq14 X0 X1
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
  have eq1290 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0
       have i₂ := eq54 X0 X0 X0 X1
       grind)
    | exact superpose eq54 eq91
    | exact resolve eq91 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1498 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X2) (σ (M.op (M.op X2 X0) (M.op X0 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq1290 X2 x
       have i₂ := eq54 X0 X2 X2 x
       grind)
    | exact superpose eq54 eq1290
    | exact resolve eq1290 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1290
  have eq36345 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq852 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq36346 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36345
  have eq36353 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36346 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq36346
    | (have j0 := eq36346 (σ X1) (σ X0)
       grind)
    | exact resolve eq36346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36372 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq36346 X0 (τ X1)
       grind)
    | exact superpose eq36346 eq17
    | (have j1 := eq36346 X0 (τ X1)
       grind)
    | exact resolve eq17 eq36346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq36346
  have eq36522 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36372 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36372
    | exact resolve eq36372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36372
  have eq36621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36522 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq36522
    | (have j0 := eq36522 X0 X1
       grind)
    | exact resolve eq36522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36522
  have eq56528 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36353 y x
       grind)
    | exact superpose eq36353 eq16
    | (have j1 := eq36353 y x
       grind)
    | exact resolve eq16 eq36353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36353
  have eq56836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56528
       have i₂ := eq36621 y x
       grind)
    | exact superpose eq36621 eq56528
    | (have j1 := eq36621 (σ y) (σ x)
       grind)
    | (have r₁ := eq56528
       have r₂ := eq36621 y x
       grind)
    | exact resolve eq56528 eq36621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36621 eq56528
  have eq56837 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56836
  have eq56866 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq304 (σ x) (σ y) X0
       have i₂ := eq56837
       grind)
    | exact superpose eq56837 eq304
    | exact resolve eq304 eq56837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56837
  have eq56967 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56866 x
       have i₂ := eq423 x x
       grind)
    | exact superpose eq423 eq56866
    | exact resolve eq56866 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq56866
  have eq57018 : (τ (σ y)) = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op (M.op x x) (M.op x x))
       have i₂ := eq56967
       grind)
    | exact superpose eq56967 eq10
    | exact resolve eq10 eq56967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56967
  have eq57067 : y = (M.op (M.op x x) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57018
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq57018
    | exact resolve eq57018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57018
  have eq57091 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 x x x
       have i₂ := eq57067
       grind)
    | exact superpose eq57067 eq9
    | exact resolve eq9 eq57067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57067
  have eq57172 : x = (M.op x y) := by grind
  clear eq57091
  have eq57219 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq304 x y X0
       have i₂ := eq57172
       grind)
    | exact superpose eq57172 eq304
    | exact resolve eq304 eq57172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq57231 : ∀ X0 X1 : G, (M.op x (M.op y X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1 x y
       have i₂ := eq57172
       grind)
    | exact superpose eq57172 eq416
    | exact resolve eq416 eq57172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq57256 : (σ x) = (M.op (σ x) (σ (M.op x (M.op y x)))) := by
    first
    | (have i₁ := eq1498 y x
       have i₂ := eq57172
       grind)
    | exact superpose eq57172 eq1498
    | exact resolve eq1498 eq57172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq57305 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq57219 x
       have i₂ := eq57231 x x
       grind)
    | exact superpose eq57231 eq57219
    | exact resolve eq57219 eq57231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57219 eq57231
  have eq63339 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57256
       have i₂ := eq57305
       grind)
    | exact superpose eq57305 eq57256
    | exact resolve eq57256 eq57305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57256 eq57305
  have eq63715 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63339
       grind)
    | exact superpose eq63339 eq16
    | exact resolve eq16 eq63339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63339
  have eq63835 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq63715
       have i₂ := eq57172
       grind)
    | exact superpose eq57172 eq63715
    | exact resolve eq63715 eq57172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57172 eq63715
  have eq63836 : False := by grind
  exact eq63836

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pxy_x_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
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
  have eq47 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
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
  have eq63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq64 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq66
    | exact resolve eq66 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq69
    | exact resolve eq69 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq196 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq47 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq48 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq359 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq88
    | (have j1 := eq82 y
       grind)
    | exact resolve eq88 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq362 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq54
    | (have j1 := eq82 (σ x)
       grind)
    | exact resolve eq54 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq385 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq12
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq428 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq49 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq49 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq49 X0 x x X3
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq471 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq462
    | exact resolve eq462 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq473 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq460 X0 X1 X2 X3
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq460
    | exact resolve eq460 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq740 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq63 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq744 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq747 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq744
    | (have j0 := eq744 X0 X1
       grind)
    | exact resolve eq744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq1229 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq209 eq47
    | exact resolve eq47 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq209 eq48
    | exact resolve eq48 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1256 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq207 eq1230
    | exact resolve eq1230 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1257 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq207 eq1229
    | exact resolve eq1229 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1683 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq428 X0 X0 X0
       grind)
    | exact superpose eq428 eq14
    | exact resolve eq14 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1684 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    grind
  have eq1685 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 X0))
       have i₂ := eq428 X0 X0 X0
       grind)
    | exact superpose eq428 eq47
    | exact resolve eq47 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1696 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq465 (M.op x (M.op x x)) x
       have i₂ := eq428 x x x
       grind)
    | exact superpose eq428 eq465
    | exact resolve eq465 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq465
  have eq1799 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1256 eq1257
    | exact resolve eq1257 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1257
  have eq1905 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq385
    | exact resolve eq385 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2405 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq27 eq1696
    | (have j0 := eq1696 (σ y) (σ x)
       grind)
    | exact resolve eq1696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq2464 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2405
       have i₂ := eq1685 sF3
       grind)
    | exact superpose eq1685 eq2405
    | exact resolve eq2405 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq5600 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq48 eq449
    | exact resolve eq449 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq449
  have eq5660 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq207 eq5600
    | exact resolve eq5600 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq5600
  have eq5805 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq473 X0 X1 X2 X3
       have i₂ := eq471 X0 X1
       grind)
    | exact superpose eq471 eq473
    | exact resolve eq473 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq473
  have eq5990 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5805 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq5805
    | exact resolve eq5805 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805
  have eq6535 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq64 eq12
    | (have j0 := eq12 (σ x) (σ X0)
       have j1 := eq64 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq64 x
       grind)
    | (have r₁ := eq12 (σ x) (σ X0)
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6557 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq6558 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq6535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq6563 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq6558 X0
       have j1 := eq12 (σ x) (σ X0)
       grind)
    | (have r₁ := eq6558 X0
       have r₂ := eq12 (σ x) (σ (k x X0))
       grind)
    | (have r₁ := eq6558 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq6558 X0
       have r₂ := eq12 (σ x) (σ X0)
       grind)
    | exact resolve eq6558 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558
  have eq6575 : ∀ X0 : G, (σ (k x X0)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq6563
    | (have j0 := eq6563 X0
       grind)
    | exact resolve eq6563 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6563
  have eq11220 : ∀ X0 : G, (k (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq742 x (τ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq742
    | (have j0 := eq742 x (τ X0)
       grind)
    | exact resolve eq742 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq742
  have eq11387 : ∀ X0 : G, (k (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11220 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11220
    | (have j0 := eq11220 X0
       grind)
    | exact resolve eq11220 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11220
  have eq11434 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (k (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (σ (τ X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11387 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11387
    | (have j0 := eq11387 X0
       grind)
    | exact resolve eq11387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11480 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (k (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (σ (τ X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11434 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11434
    | (have j0 := eq11434 X0
       grind)
    | exact resolve eq11434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11434
  have eq11525 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (k (σ x) X0) ≠ (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11480 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11480
    | (have j0 := eq11480 X0
       grind)
    | exact resolve eq11480 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11480
  have eq11565 : ∀ X0 : G, (k (σ x) X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11525 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11525
    | (have j0 := eq11525 X0
       grind)
    | exact resolve eq11525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11525
  have eq16261 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq26184 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq385 X2
       have i₂ := eq1683 X2 X0 X1
       grind)
    | exact superpose eq1683 eq385
    | exact resolve eq385 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq27492 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5660 sF3 sF3
       have i₂ := eq50 sF3 sF3
       grind)
    | exact superpose eq50 eq5660
    | exact resolve eq5660 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq27545 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op y (M.op (M.op x y) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq27492
       have i₂ := eq1685 sF3
       grind)
    | exact superpose eq1685 eq27492
    | exact resolve eq27492 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq27492
  have eq33868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq71 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq33868
    | exact resolve eq33868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33868
  have eq33880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33869
       have r₂ := eq28
       grind)
    | exact resolve eq33869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33869
  have eq33882 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq33880
    | exact resolve eq33880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33880
  have eq33889 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq33882 eq47
    | exact resolve eq47 eq33882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33975 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq33882 eq26184
    | exact resolve eq26184 eq33882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26184 eq33882
  have eq40615 : (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op y (M.op (M.op x y) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2464 eq33975
    | exact resolve eq33975 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464 eq33975
  have eq40774 : (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op y (M.op (M.op x y) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq40615
    | exact resolve eq40615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40615
  have eq40788 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op y (M.op (M.op x y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27545 eq40774
    | exact resolve eq40774 eq27545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27545 eq40774
  have eq46627 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40788 eq1905
    | exact resolve eq1905 eq40788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905 eq40788
  have eq46707 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1799 eq46627
    | exact resolve eq46627 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq46627
  have eq47614 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq46707 eq33889
    | exact resolve eq33889 eq46707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33889 eq46707
  have eq47682 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq47614
  have eq47723 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq47682 eq362
    | exact resolve eq362 eq47682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq47727 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq47682
  have eq47840 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq47723
  have eq47886 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq47840
    | exact resolve eq47840 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47840
  have eq47915 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq47727 eq58
    | exact resolve eq58 eq47727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq47916 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq47727 eq71
    | exact resolve eq71 eq47727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq47727
  have eq47925 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq47916
  have eq47933 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq47915
    | exact resolve eq47915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47915
  have eq47941 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq47925
       grind)
    | exact superpose eq47925 eq47
    | exact resolve eq47 eq47925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48089 : x = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq196 eq47941
    | exact resolve eq47941 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47941
  have eq53034 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq47886
       grind)
    | exact superpose eq47886 eq47
    | exact resolve eq47 eq47886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq53193 : x = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq196 eq53034
    | exact resolve eq53034 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq53034
  have eq53352 : y ≠ (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by grind
  have eq61828 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0)))) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq5990 X0 x x X1
       have i₂ := eq47886
       grind)
    | exact superpose eq47886 eq5990
    | exact resolve eq5990 eq47886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47886
  have eq61830 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0)))) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq5990 X0 x x X1
       have i₂ := eq47925
       grind)
    | exact superpose eq47925 eq5990
    | exact resolve eq5990 eq47925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990 eq47925
  have eq62463 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq61830 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq61830
    | exact resolve eq61830 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61830
  have eq62464 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61828 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq61828
    | exact resolve eq61828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61828
  have eq62734 : y = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq385 y
       have i₂ := eq62463 y
       grind)
    | exact superpose eq62463 eq385
    | exact resolve eq385 eq62463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62463
  have eq63082 : y = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62734
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62734
    | exact resolve eq62734 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62734
  have eq64346 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq63082 eq48089
    | exact resolve eq48089 eq63082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48089 eq63082
  have eq64422 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq64346
  have eq64502 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq358
       have i₂ := eq64422
       grind)
    | exact superpose eq64422 eq358
    | exact resolve eq358 eq64422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64507 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq64573 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50 x x
       have i₂ := eq64422
       grind)
    | exact superpose eq64422 eq50
    | exact resolve eq50 eq64422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq64422
  have eq64637 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq64502
  have eq64673 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64573
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64573
    | exact resolve eq64573 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64573
  have eq64707 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64637
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64637
    | exact resolve eq64637 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64637
  have eq64749 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq64507
       grind)
    | exact superpose eq64507 eq45
    | exact resolve eq45 eq64507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64767 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64749
    | exact resolve eq64749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64749
  have eq65902 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq359
       have i₂ := eq64673
       grind)
    | exact superpose eq64673 eq359
    | exact resolve eq359 eq64673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq64673
  have eq66099 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq65902
    | exact resolve eq65902 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65902
  have eq66748 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64707
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq64707
    | (have j1 := eq82 (σ x)
       grind)
    | exact resolve eq64707 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182733 : y = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq385 y
       have i₂ := eq62464 y
       grind)
    | exact superpose eq62464 eq385
    | exact resolve eq385 eq62464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62464
  have eq183327 : y = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq182733
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq182733
    | exact resolve eq182733 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182733
  have eq198263 : x = y ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq183327 eq53193
    | exact resolve eq53193 eq183327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53193 eq183327
  have eq198385 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq198263
  have eq198520 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq198385
       grind)
    | exact superpose eq198385 eq82
    | (have j0 := eq82 x
       grind)
    | exact resolve eq82 eq198385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq198521 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq198520
  have eq198551 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq198521
       have i₂ := eq47933
       grind)
    | exact superpose eq47933 eq198521
    | exact resolve eq198521 eq47933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47933
  have eq198589 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq385 x
       have i₂ := eq198521
       grind)
    | exact superpose eq198521 eq385
    | exact resolve eq385 eq198521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198772 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) ∨ y = (M.op x x) := by grind
  clear eq198551
  have eq198849 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq198589
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq198589
    | exact resolve eq198589 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198589
  have eq198869 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq198772
       have r₂ := eq53352
       grind)
    | exact resolve eq198772 eq53352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53352 eq198772
  have eq203055 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq64767 eq11565
    | (have j0 := eq11565 (σ y)
       grind)
    | exact resolve eq11565 eq64767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq64767
  have eq203077 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq203055
       have r₂ := eq66748
       grind)
    | exact resolve eq203055 eq66748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203055
  have eq203084 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq203077
    | exact resolve eq203077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203077
  have eq203189 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq203084 eq393
    | exact resolve eq393 eq203084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq203084
  have eq203310 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq203189
    | exact resolve eq203189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203189
  have eq203361 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq203310
    | exact resolve eq203310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203310
  have eq225650 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq198869
  have eq225836 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq225650
  have eq226030 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq225836
       grind)
    | exact superpose eq225836 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq225836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225836
  have eq226032 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq226030
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq226030
    | exact resolve eq226030 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226030
  have eq226033 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq226032
  have eq226049 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq226033
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq226033
    | exact resolve eq226033 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226033
  have eq239358 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq198521
       have i₂ := eq226049
       grind)
    | exact superpose eq226049 eq198521
    | exact resolve eq198521 eq226049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198521
  have eq239566 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq226049
  have eq239584 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq239358
  have eq239748 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq239584
       have r₂ := eq239566
       grind)
    | exact resolve eq239584 eq239566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239566 eq239584
  have eq239795 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq385 x
       have i₂ := eq239748
       grind)
    | exact superpose eq239748 eq385
    | exact resolve eq385 eq239748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239748
  have eq240110 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq239795
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq239795
    | exact resolve eq239795 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239795
  have eq291812 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6557 y
       have i₂ := eq64507
       grind)
    | exact superpose eq64507 eq6557
    | (have j0 := eq6557 y
       grind)
    | exact resolve eq6557 eq64507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq291911 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq291812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq291812
    | exact resolve eq291812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291812
  have eq291982 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq291911
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq291911
    | exact resolve eq291911 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291911
  have eq292009 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq291982
    | exact resolve eq291982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291982
  have eq292024 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq292009
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq292009
    | exact resolve eq292009 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292009
  have eq292032 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq292024
       have r₂ := eq66748
       grind)
    | exact resolve eq292024 eq66748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292024
  have eq412354 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq292032
  have eq412825 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq412354 eq1684
    | exact resolve eq1684 eq412354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq412354
  have eq413168 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq412825
    | exact resolve eq412825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412825
  have eq440348 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6575 y
       have i₂ := eq64507
       grind)
    | exact superpose eq64507 eq6575
    | (have j0 := eq6575 y
       grind)
    | exact resolve eq6575 eq64507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575 eq64507
  have eq440453 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq440348
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq440348
    | exact resolve eq440348 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440348
  have eq440534 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq440453
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq440453
    | exact resolve eq440453 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440453
  have eq440583 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq440534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq440534
    | exact resolve eq440534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440534
  have eq440619 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq440583
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq440583
    | exact resolve eq440583 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440583
  have eq440639 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq440619
       have r₂ := eq66748
       grind)
    | exact resolve eq440619 eq66748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66748 eq440619
  have eq440671 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq440639 eq385
    | exact resolve eq385 eq440639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq440639
  have eq441064 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq440671
    | exact resolve eq440671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440671
  have eq443897 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq441064 eq12
    | exact resolve eq12 eq441064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441064
  have eq444054 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq443897
  have eq444055 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq444054
  have eq448685 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq444055 eq66099
    | exact resolve eq66099 eq444055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444055
  have eq448713 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq448685
  have eq3155935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq203361 eq66099
    | exact resolve eq66099 eq203361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66099 eq203361
  have eq3156044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3155935
  have eq3156079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3156044
       have r₂ := eq28
       grind)
    | exact resolve eq3156044 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156044
  have eq3156410 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3156079 eq448713
    | exact resolve eq448713 eq3156079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448713 eq3156079
  have eq3156663 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3156410
  have eq3156827 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq3156663
    | exact resolve eq3156663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156663
  have eq3156828 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3156827
  have eq3157114 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3156828 eq413168
    | exact resolve eq413168 eq3156828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413168 eq3156828
  have eq3157347 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq3157114
  have eq3162133 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3157347 eq64707
    | exact resolve eq64707 eq3157347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64707 eq3157347
  have eq3162332 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq3162133
  have eq3162412 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3162332 eq30
    | exact resolve eq30 eq3162332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162332
  have eq3162854 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3162412
    | exact resolve eq3162412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162412
  have eq3162855 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq3162854
  have eq3162861 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq3162855 eq29
    | exact resolve eq29 eq3162855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162855
  have eq3163769 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3162861
    | exact resolve eq3162861 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3162861
  have eq3164679 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3163769 eq240110
    | exact resolve eq240110 eq3163769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240110 eq3163769
  have eq3165481 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3164679
  have eq3165890 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3165481
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3165481
    | exact resolve eq3165481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165481
  have eq3165891 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3165890
  have eq3166112 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3165891 eq30
    | exact resolve eq30 eq3165891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165891
  have eq3166554 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3166112
    | exact resolve eq3166112 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166112
  have eq3166555 : x = (M.op x y) ∨ x = y := by grind
  clear eq3166554
  have eq3167375 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3166555 eq198849
    | exact resolve eq198849 eq3166555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198849 eq3166555
  have eq3168135 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3167375
  have eq3299414 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq3317409 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq198385
       have i₂ := eq3299414
       grind)
    | exact superpose eq3299414 eq198385
    | exact resolve eq198385 eq3299414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198385 eq3299414
  have eq3317616 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3317409
  have eq3322902 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3168135
       have i₂ := eq3317616
       grind)
    | exact superpose eq3317616 eq3168135
    | exact resolve eq3168135 eq3317616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168135 eq3317616
  have eq3323747 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3322902
  have eq3324333 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3323747 eq30
    | exact resolve eq30 eq3323747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3323747
  have eq3324792 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3324333
    | exact resolve eq3324333 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3324333
  have eq3324793 : x = y := by grind
  clear eq3324792
  have eq3324799 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3324793
       grind)
    | exact superpose eq3324793 eq19
    | exact resolve eq19 eq3324793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3324800 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3324793
       grind)
    | exact superpose eq3324793 eq25
    | exact resolve eq25 eq3324793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3324793
  have eq3325623 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3324800
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3324800
    | exact resolve eq3324800 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324800
  have eq3325662 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3325623 eq27
    | exact resolve eq27 eq3325623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3325623
  have eq3326427 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq358
       have i₂ := eq3324799
       grind)
    | exact superpose eq3324799 eq358
    | exact resolve eq358 eq3324799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq3326701 : x = (k x (M.op x y)) := by grind
  have eq3327000 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq3324799
       grind)
    | exact superpose eq3324799 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq3324799
       grind)
    | exact resolve eq12 eq3324799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324799
  have eq3327370 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3327000
  have eq3327744 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3326427
    | exact resolve eq3326427 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326427
  have eq3328330 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  have eq3352761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16261 x x
       have i₂ := eq3327370
       grind)
    | exact superpose eq3327370 eq16261
    | (have j0 := eq16261 x x
       grind)
    | exact resolve eq16261 eq3327370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327370
  have eq3352763 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3352761
  have eq3352764 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3352763
  have eq3352786 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3352764
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3352764
    | exact resolve eq3352764 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352764
  have eq3352900 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3325662 eq3352786
    | exact resolve eq3352786 eq3325662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352786
  have eq3353001 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3352900
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3352900
    | exact resolve eq3352900 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352900
  have eq3353089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3325662 eq3353001
    | exact resolve eq3353001 eq3325662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353001
  have eq3353172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3353089
    | exact resolve eq3353089 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353089
  have eq3353236 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3353172
       have r₂ := eq28
       grind)
    | exact resolve eq3353172 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353172
  have eq3353422 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3353236 eq28
    | exact resolve eq28 eq3353236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3353790 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3353236 eq3328330
    | exact resolve eq3328330 eq3353236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328330 eq3353236
  have eq3357906 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3353790 eq3327744
    | exact resolve eq3327744 eq3353790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327744 eq3353790
  have eq3358044 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3357906
  have eq3358125 : x = (M.op x y) := by
    first
    | (have r₁ := eq3358044
       have r₂ := eq3353422
       grind)
    | exact resolve eq3358044 eq3353422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353422 eq3358044
  have eq3358231 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3358125 eq21
    | exact resolve eq21 eq3358125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3359493 : x = (k x x) := by
    first
    | exact superpose eq3358125 eq3326701
    | exact resolve eq3326701 eq3358125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326701 eq3358125
  have eq3359902 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3358231
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3358231
    | exact resolve eq3358231 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358231
  have eq3361781 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16261 x x
       have i₂ := eq3359493
       grind)
    | exact superpose eq3359493 eq16261
    | (have j0 := eq16261 x x
       grind)
    | exact resolve eq16261 eq3359493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16261 eq3359493
  have eq3361784 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3361781
  have eq3361785 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3361784
  have eq3361843 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3361785
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3361785
    | exact resolve eq3361785 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3361785
  have eq3361936 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3325662 eq3361843
    | exact resolve eq3361843 eq3325662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325662 eq3361843
  have eq3362021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3359902 eq3361936
    | exact resolve eq3361936 eq3359902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3359902 eq3361936
  have eq3362100 : False := by grind
  exact eq3362100
