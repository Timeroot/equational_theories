import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq24 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
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
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq84
    | exact resolve eq84 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq84
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq499 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq123
    | exact resolve eq123 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq500 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq499
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq499
    | exact resolve eq499 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq517 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq500
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq500
    | (have j1 := eq55 y x
       grind)
    | exact resolve eq500 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq500
  have eq518 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq517
  have eq3989 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq518
       grind)
    | exact superpose eq518 eq10
    | exact resolve eq10 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq4036 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq3989
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq3989
    | exact resolve eq3989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq4037 : (M.op y y) = (M.op x x) := by grind
  clear eq4036
  have eq4086 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq75 y y
       have i₂ := eq4037
       grind)
    | exact superpose eq4037 eq75
    | exact resolve eq75 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037
  have eq4115 : x = y := by
    first
    | (have i₁ := eq4086
       have i₂ := eq75 x x
       grind)
    | exact superpose eq75 eq4086
    | exact resolve eq4086 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq4086
  have eq4185 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4115
       grind)
    | exact superpose eq4115 eq16
    | exact resolve eq16 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq4186 : False := by grind
  exact eq4186

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq348 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq348
    | (have j0 := eq348 (σ X0) (σ X1)
       grind)
    | exact resolve eq348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq348 X1 (τ X0)
       grind)
    | exact superpose eq348 eq18
    | (have j1 := eq348 X1 (τ X0)
       grind)
    | exact resolve eq18 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq367 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq348 (τ X1) X0
       grind)
    | exact superpose eq348 eq17
    | (have j1 := eq348 (τ X1) X0
       grind)
    | exact resolve eq17 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq443 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq349 y x
       grind)
    | exact superpose eq349 eq16
    | (have j1 := eq349 y x
       grind)
    | exact resolve eq16 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq349 X0 X0
       grind)
    | exact superpose eq349 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq349 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq349 X1 X1
       grind)
    | exact resolve eq12 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq459 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq452 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq514 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq643 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq514
    | exact resolve eq514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq1403 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq356 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq356
    | (have j0 := eq356 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq356 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1426 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1403 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1403
    | (have j0 := eq1403 X0
       grind)
    | exact resolve eq1403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1428 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1426 X0
       have i₂ := eq88 (τ X0) (τ X0)
       grind)
    | exact superpose eq88 eq1426
    | (have j0 := eq1426 X0
       grind)
    | exact resolve eq1426 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1426
  have eq2074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq443
       have i₂ := eq348 y x
       grind)
    | exact superpose eq348 eq443
    | (have j1 := eq348 (σ y) (σ x)
       grind)
    | exact resolve eq443 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq2077 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2074
  have eq2080 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq2077
       grind)
    | exact superpose eq2077 eq9
    | exact resolve eq9 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11532 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1428 X0
       have i₂ := eq367 (τ X0) X0
       grind)
    | exact superpose eq367 eq1428
    | (have j0 := eq1428 X0
       have j1 := eq367 (τ X0) X0
       grind)
    | exact resolve eq1428 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq1428
  have eq11558 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq11532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11532
  have eq11572 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11558 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11558
    | (have j0 := eq11558 X0
       grind)
    | exact resolve eq11558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11558
  have eq11926 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11572 X0
       grind)
    | exact superpose eq11572 eq85
    | (have j1 := eq11572 X0
       grind)
    | (have r₁ := eq85 (τ X0) X1
       have r₂ := eq11572 X0
       grind)
    | exact resolve eq85 eq11572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572
  have eq11991 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11926
  have eq12810 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11991 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11991
    | (have j0 := eq11991 (σ X0) X1
       grind)
    | exact resolve eq11991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11991
  have eq12893 : ∀ X0 X1 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12810 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12810
    | (have j0 := eq12810 X0 X1
       grind)
    | exact resolve eq12810 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12810
  have eq12901 : ∀ X0 X1 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12893 X0 X1
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq12893
    | (have j0 := eq12893 X0 X1
       grind)
    | exact resolve eq12893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12893
  have eq13120 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k X0 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq12901 X0 X1
       grind)
    | exact superpose eq12901 eq10
    | (have j1 := eq12901 X0 X1
       grind)
    | exact resolve eq10 eq12901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12901
  have eq13153 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13120 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13120
    | (have j0 := eq13120 X0 X1
       grind)
    | exact resolve eq13120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120
  have eq13174 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13153 X0 X1
       have i₂ := eq348 X0 X0
       grind)
    | exact superpose eq348 eq13153
    | (have j0 := eq13153 X0 X1
       have j1 := eq348 X1 X0
       grind)
    | exact resolve eq13153 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153
  have eq13225 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13174 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq13174 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13174 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13174
  have eq13417 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13225 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13225
  have eq13418 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13417 X0
       grind)
    | (have r₁ := eq13417 X0
       have r₂ := eq52 X0
       grind)
    | exact resolve eq13417 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13417
  have eq13438 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13418 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq13418
    | exact resolve eq13418 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq13418
  have eq13476 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq13438 (σ X0)
       grind)
    | exact superpose eq13438 eq22
    | exact resolve eq22 eq13438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq13492 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13476 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13476
    | exact resolve eq13476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13476
  have eq110919 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2080 (σ y)
       have i₂ := eq2077
       grind)
    | exact superpose eq2077 eq2080
    | exact resolve eq2080 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq111213 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op y x) := by grind
  clear eq110919
  have eq111464 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq643 (σ x) (M.op (σ y) (σ y))
       have i₂ := eq111213
       grind)
    | exact superpose eq111213 eq643
    | exact resolve eq643 eq111213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111213
  have eq111721 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2077
       have i₂ := eq111464
       grind)
    | exact superpose eq111464 eq2077
    | exact resolve eq2077 eq111464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077 eq111464
  have eq111901 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq111721
  have eq111942 : x = (k (τ (σ x)) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13492 x
       have i₂ := eq111901
       grind)
    | exact superpose eq111901 eq13492
    | exact resolve eq13492 eq111901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13492 eq111901
  have eq112215 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq111942
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111942
    | exact resolve eq111942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111942
  have eq112290 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq348 x x
       have i₂ := eq112215
       grind)
    | exact superpose eq112215 eq348
    | (have j0 := eq348 x x
       grind)
    | exact resolve eq348 eq112215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq112215
  have eq112325 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq112290
  have eq112359 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq112325
       grind)
    | exact superpose eq112325 eq9
    | exact resolve eq9 eq112325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120598 : y = (M.op x (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112359 y
       have i₂ := eq112325
       grind)
    | exact superpose eq112325 eq112359
    | exact resolve eq112359 eq112325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112359
  have eq120892 : y = (M.op x (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq120598
  have eq121124 : (M.op y x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq643 x (M.op y y)
       have i₂ := eq120892
       grind)
    | exact superpose eq120892 eq643
    | exact resolve eq643 eq120892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq120892
  have eq121377 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112325
       have i₂ := eq121124
       grind)
    | exact superpose eq121124 eq112325
    | exact resolve eq112325 eq121124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112325 eq121124
  have eq121545 : x = (M.op x x) := by grind
  clear eq121377
  have eq121582 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq85 x x
       have i₂ := eq121545
       grind)
    | exact superpose eq121545 eq85
    | (have r₁ := eq85 x x
       have r₂ := eq121545
       grind)
    | exact resolve eq85 eq121545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq121603 : x = (k x x) := by
    first
    | (have i₁ := eq13438 x
       have i₂ := eq121545
       grind)
    | exact superpose eq121545 eq13438
    | exact resolve eq13438 eq121545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13438 eq121545
  have eq121773 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq121582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121582
  have eq121850 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq459 x X0
       have i₂ := eq121603
       grind)
    | exact superpose eq121603 eq459
    | (have j0 := eq459 x X0
       grind)
    | exact resolve eq459 eq121603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq121603
  have eq121962 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq121850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121850
  have eq125769 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq121962 (σ X0)
       grind)
    | exact superpose eq121962 eq15
    | exact resolve eq15 eq121962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121962
  have eq125866 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq125769 X0
       have i₂ := eq121773 X0
       grind)
    | exact superpose eq121773 eq125769
    | exact resolve eq125769 eq121773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121773 eq125769
  have eq128356 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125866 y
       grind)
    | exact superpose eq125866 eq16
    | (have r₁ := eq16
       have r₂ := eq125866 y
       grind)
    | exact resolve eq16 eq125866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125866
  have eq128633 : False := by grind
  exact eq128633

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op X0 X0)
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = X0 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq58 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq120 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq23 X1 X4 X0 X2
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq51 X0 X1
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 (σ X0)) (M.op (σ X2) (σ X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) X1 (σ X0)
       have i₂ := eq51 X0 X2
       grind)
    | exact superpose eq51 eq9
    | (have j1 := eq51 X0 X2
       grind)
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq233 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq234 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq329 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq84 (τ X1) X0
       grind)
    | exact superpose eq84 eq17
    | (have j1 := eq84 (τ X1) X0
       grind)
    | exact resolve eq17 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq373 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq35
    | exact resolve eq35 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq23 X1 X1 X0 X2
       grind)
    | exact superpose eq23 eq35
    | exact resolve eq35 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq24 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq374
    | exact resolve eq374 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq616 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq538
    | exact resolve eq538 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq538
    | exact resolve eq538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq616 X0 X1 X2
       have i₂ := eq617 (M.op X0 X2) X1
       grind)
    | exact superpose eq617 eq616
    | exact resolve eq616 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq818 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq120 X4 (M.op X2 X0) (M.op X0 X0) X3 X1
       have i₂ := eq26 X0 X2
       grind)
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 (M.op X0 X1) X0 X1 (M.op X0 X1) X2
       have i₂ := eq24 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq120
    | exact resolve eq120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq917 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq847 X0 X1 X2
       have i₂ := eq617 X0 X2
       grind)
    | exact superpose eq617 eq847
    | exact resolve eq847 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq926 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq818 X0 X1 X2 X3 X4
       have i₂ := eq617 (M.op X2 X0) X1
       grind)
    | exact superpose eq617 eq818
    | exact resolve eq818 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq938 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op X2 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq926 X0 X1 X2 X3 X4
       have i₂ := eq649 X2 X1 X0
       grind)
    | exact superpose eq649 eq926
    | exact resolve eq926 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1057 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq917 X0 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq917
    | exact resolve eq917 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X1 X1
       have i₂ := eq917 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq917 eq23
    | exact resolve eq23 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1118 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 (M.op x X0))
       have i₂ := eq917 X0 (M.op x X0) x
       grind)
    | exact superpose eq917 eq34
    | exact resolve eq34 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq917
  have eq1144 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 X1
       have i₂ := eq649 X0 X1 X1
       grind)
    | exact superpose eq649 eq1118
    | exact resolve eq1118 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1296 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq1057 X1 X0
       grind)
    | exact superpose eq1057 eq9
    | exact resolve eq9 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 (M.op X1 X0) X2 (M.op X0 X0)
       have i₂ := eq1296 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq1296 eq35
    | exact resolve eq35 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1296
  have eq1678 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1636 X0 X1 X2
       have i₂ := eq617 X0 X1
       grind)
    | exact superpose eq617 eq1636
    | exact resolve eq1636 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq1636
  have eq1868 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1095 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq1095 X0 X1 X2
       grind)
    | (have i₁ := eq1095 X1 (M.op X0 X1) X2
       have i₂ := eq1095 X0 X1 X2
       grind)
    | exact superpose eq1095 eq1095
    | exact resolve eq1095 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1932 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1144 X1 X2
       have i₂ := eq1095 X1 X2 X0
       grind)
    | (have i₁ := eq1144 X0 (M.op X2 X0)
       have i₂ := eq1095 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1095 eq1144
    | exact resolve eq1144 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1057 X2 X1
       have i₂ := eq1095 X1 X2 X0
       grind)
    | (have i₁ := eq1057 (M.op X2 X0) X0
       have i₂ := eq1095 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1095 eq1057
    | exact resolve eq1057 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1995 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1868 X0 X1 X2 X3
       have i₂ := eq649 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq649 eq1868
    | exact resolve eq1868 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq1868
  have eq2016 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1995 X0 X1 X2 X3
       have i₂ := eq1932 X0 X1 X2
       grind)
    | exact superpose eq1932 eq1995
    | exact resolve eq1995 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932 eq1995
  have eq2320 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq243 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq243
    | exact resolve eq243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq2426 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2320 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2320
    | (have j0 := eq2320 X0 X1
       grind)
    | exact resolve eq2320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2430 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2426 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq2426 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2426 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2433 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2430 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2430
    | (have j0 := eq2430 X0 X1
       grind)
    | exact resolve eq2430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2430
  have eq3067 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1933 X0 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq1933
    | exact resolve eq1933 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq4868 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X2)) (M.op X0 X0)) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) ∨ (M.op (σ X2) X0) = (σ (k (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq228 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq228
    | (have j0 := eq228 X2 X1 X2
       grind)
    | exact resolve eq228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq5067 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op (M.op X1 (σ X2)) (M.op X0 X0)) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4868 X0 X1 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq4868
    | (have j0 := eq4868 X0 X1 X2
       grind)
    | exact resolve eq4868 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868
  have eq5076 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X2)) (M.op X0 X0)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5067 X0 X1 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq5067 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq5067 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5067
  have eq8372 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2433 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2433
    | exact resolve eq2433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2433 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2433
    | exact resolve eq2433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq8935 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq8372 (τ X1) X0
       grind)
    | exact superpose eq8372 eq17
    | (have j1 := eq8372 (τ X1) X0
       grind)
    | exact resolve eq17 eq8372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq8945 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8372 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8372
  have eq10453 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq329
    | exact resolve eq329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq10568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10453 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10453
    | (have j0 := eq10453 X0 X1
       grind)
    | exact resolve eq10453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq14050 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq938 X1 X1 X0 X2 X3
       have i₂ := eq1144 X0 X1
       grind)
    | exact superpose eq1144 eq938
    | exact resolve eq938 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq1144
  have eq16050 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X2)) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5076 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5076
    | exact resolve eq5076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5076
  have eq68055 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3067 X0 (M.op x x)
       have i₂ := eq16050 X0 X0 x
       grind)
    | exact superpose eq16050 eq3067
    | (have j1 := eq16050 X1 X1 X0
       grind)
    | exact resolve eq3067 eq16050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067
  have eq68173 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op x x) X1
       have i₂ := eq16050 x x x
       grind)
    | exact superpose eq16050 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq16050 X0 X1 X1
       grind)
    | exact resolve eq33 eq16050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq16050
  have eq68384 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68173 X0 X1
       have j1 := eq62 X0 X1 X1
       grind)
    | (have r₁ := eq68173 X0 X1
       have r₂ := eq62 X0 X1 X0
       grind)
    | exact resolve eq68173 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq68173
  have eq68401 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68055 X0 X1
       have i₂ := eq1678 X0 X1 X0
       grind)
    | exact superpose eq1678 eq68055
    | (have j0 := eq68055 X0 X1
       grind)
    | exact resolve eq68055 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678 eq68055
  have eq69339 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68384 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68384
  have eq69340 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq69339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69339
  have eq70338 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69340 (σ X0)
       grind)
    | exact superpose eq69340 eq15
    | exact resolve eq15 eq69340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70338 X0
       have i₂ := eq69340 X0
       grind)
    | exact superpose eq69340 eq70338
    | exact resolve eq70338 eq69340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69340 eq70338
  have eq72964 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq538 (σ X0) (σ X0)
       have i₂ := eq70391 X0
       grind)
    | exact superpose eq70391 eq538
    | exact resolve eq538 eq70391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70391
  have eq89482 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq68401 X0 X1
       grind)
    | exact superpose eq68401 eq9
    | (have j1 := eq68401 X0 X1
       grind)
    | exact resolve eq9 eq68401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68401
  have eq102002 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op (M.op X3 X1) X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2016 X0 X0 (M.op X1 X1) X3
       have i₂ := eq89482 X0 X1
       grind)
    | exact superpose eq89482 eq2016
    | (have j1 := eq89482 X1 X0
       grind)
    | exact resolve eq2016 eq89482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016 eq89482
  have eq102178 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X3 X1) X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq102002 X0 X1 x X3
       have i₂ := eq14050 (M.op X3 X1) X0 x X0
       grind)
    | exact superpose eq14050 eq102002
    | (have j0 := eq102002 X0 X1 x X3
       grind)
    | exact resolve eq102002 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14050 eq102002
  have eq126223 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8935 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8935
    | exact resolve eq8935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935
  have eq126628 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126223 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126223
    | (have j0 := eq126223 X0 X1
       grind)
    | exact resolve eq126223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126223
  have eq330322 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8386 y x
       grind)
    | exact superpose eq8386 eq16
    | (have j1 := eq8386 y x
       grind)
    | exact resolve eq16 eq8386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386
  have eq333141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq330322
       have i₂ := eq126628 y x
       grind)
    | exact superpose eq126628 eq330322
    | (have j1 := eq126628 y x
       grind)
    | (have r₁ := eq330322
       have r₂ := eq126628 y x
       grind)
    | exact resolve eq330322 eq126628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126628
  have eq333144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq330322
       have i₂ := eq10568 y x
       grind)
    | exact superpose eq10568 eq330322
    | (have j1 := eq10568 y x
       grind)
    | (have r₁ := eq330322
       have r₂ := eq10568 y x
       grind)
    | exact resolve eq330322 eq10568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10568 eq330322
  have eq333145 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq333144
  have eq333148 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
  clear eq333141
  have eq335203 : (M.op x y) = (τ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq333145
       grind)
    | exact superpose eq333145 eq10
    | exact resolve eq10 eq333145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333145
  have eq335535 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq335203
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq335203
    | exact resolve eq335203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335203
  have eq337925 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq335535
       grind)
    | exact superpose eq335535 eq9
    | exact resolve eq9 eq335535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341560 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq333148
       grind)
    | exact superpose eq333148 eq10
    | exact resolve eq10 eq333148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333148
  have eq341898 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq341560
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq341560
    | exact resolve eq341560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341560
  have eq341946 : x = (k y x) := by
    first
    | (have j1 := eq8945 y x
       grind)
    | (have r₁ := eq341898
       have r₂ := eq8945 y x
       grind)
    | exact resolve eq341898 eq8945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8945 eq341898
  have eq365506 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq337925 y
       have i₂ := eq335535
       grind)
    | exact superpose eq335535 eq337925
    | exact resolve eq337925 eq335535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337925
  have eq365811 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq365506
  have eq368149 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq538 x (M.op y y)
       have i₂ := eq365811
       grind)
    | exact superpose eq365811 eq538
    | exact resolve eq538 eq365811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq365811
  have eq370570 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq335535
       have i₂ := eq368149
       grind)
    | exact superpose eq368149 eq335535
    | exact resolve eq335535 eq368149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335535 eq368149
  have eq370742 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq370570
  have eq372795 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq373 y x
       have i₂ := eq370742
       grind)
    | exact superpose eq370742 eq373
    | exact resolve eq373 eq370742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372812 : x = (M.op y (M.op y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1057 y x
       have i₂ := eq370742
       grind)
    | exact superpose eq370742 eq1057
    | exact resolve eq1057 eq370742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq379842 : y = (M.op y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 y
       have i₂ := eq372795
       grind)
    | exact superpose eq372795 eq24
    | exact resolve eq24 eq372795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq372795
  have eq393778 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq379842
       have i₂ := eq370742
       grind)
    | exact superpose eq370742 eq379842
    | exact resolve eq379842 eq370742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370742 eq379842
  have eq394022 : y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq393778
  have eq396894 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq372812
       have i₂ := eq394022
       grind)
    | exact superpose eq394022 eq372812
    | exact resolve eq372812 eq394022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372812 eq394022
  have eq397083 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq396894
  have eq401055 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq397083
       grind)
    | exact superpose eq397083 eq26
    | exact resolve eq26 eq397083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq397083
  have eq413846 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102178 x y x
       have i₂ := eq401055 x
       grind)
    | exact superpose eq401055 eq102178
    | (have j0 := eq102178 x y x
       grind)
    | exact resolve eq102178 eq401055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102178 eq401055
  have eq414094 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq413846
       have r₂ := eq12 x x
       grind)
    | exact resolve eq413846 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413846
  have eq414109 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414094
       have i₂ := eq341946
       grind)
    | exact superpose eq341946 eq414094
    | exact resolve eq414094 eq341946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341946 eq414094
  have eq414110 : x = (M.op x y) := by grind
  clear eq414109
  have eq416150 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq373 y x
       have i₂ := eq414110
       grind)
    | exact superpose eq414110 eq373
    | exact resolve eq373 eq414110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq416344 : x = (M.op y y) := by
    first
    | (have i₁ := eq416150
       have i₂ := eq414110
       grind)
    | exact superpose eq414110 eq416150
    | exact resolve eq416150 eq414110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416150
  have eq418329 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72964 y
       have i₂ := eq416344
       grind)
    | exact superpose eq416344 eq72964
    | exact resolve eq72964 eq416344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72964 eq416344
  have eq460136 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq418329
       grind)
    | exact superpose eq418329 eq16
    | exact resolve eq16 eq418329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418329
  have eq460563 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq460136
       have i₂ := eq414110
       grind)
    | exact superpose eq414110 eq460136
    | exact resolve eq460136 eq414110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414110 eq460136
  have eq460564 : False := by grind
  exact eq460564

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq122 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 X2
       have i₂ := eq122 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq122 X0 X0
       grind)
    | exact superpose eq122 eq9
    | (have j1 := eq122 X0 X1
       grind)
    | exact resolve eq9 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq122 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq122 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq122 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq122 X0 X0
       grind)
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq201 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq199 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq199 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq275 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq986 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq29 X0 X0 X2 X1
       grind)
    | exact superpose eq29 eq40
    | exact resolve eq40 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40
  have eq1447 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq986 X0 (M.op X0 X0) X2 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq986
    | exact resolve eq986 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1792 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op X3 X0) ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1447 X0 (M.op x (M.op X3 x)) X3
       have i₂ := eq177 X0 X3 x x
       grind)
    | exact superpose eq177 eq1447
    | (have j1 := eq177 X0 X3 x X3
       grind)
    | exact resolve eq1447 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq5023 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq1792 X0 X1
       grind)
    | (have i₁ := eq30 X0
       have i₂ := eq1792 X0 X0
       grind)
    | exact superpose eq1792 eq30
    | (have j1 := eq1792 X0 X1
       grind)
    | exact resolve eq30 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1792
  have eq6056 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5023 X0 X1
       have i₂ := eq122 X0 X1
       grind)
    | (have i₁ := eq5023 X1 X1
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq5023
    | (have j0 := eq5023 X0 X1
       have j1 := eq122 X0 X1
       grind)
    | exact resolve eq5023 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq5023
  have eq6159 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6056 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6056
  have eq7385 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1447 X1 X0 X1
       have i₂ := eq6159 X0 X1
       grind)
    | exact superpose eq6159 eq1447
    | (have j1 := eq6159 X0 X1
       grind)
    | exact resolve eq1447 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq6159
  have eq7457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7385 X0 X1
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq7385 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | (have r₁ := eq7385 X1 X1
       have r₂ := eq275 X1 X1
       grind)
    | exact resolve eq7385 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq7385
  have eq7848 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq7457 (σ X0) (σ X1)
       grind)
    | exact superpose eq7457 eq15
    | exact resolve eq15 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7881 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7848 X0 X1
       have i₂ := eq7457 X0 X1
       grind)
    | exact superpose eq7457 eq7848
    | exact resolve eq7848 eq7457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7457 eq7848
  have eq8007 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7881 x y
       grind)
    | exact superpose eq7881 eq16
    | (have r₁ := eq16
       have r₂ := eq7881 x y
       grind)
    | exact resolve eq16 eq7881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7881
  have eq8035 : False := by grind
  exact eq8035

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq201 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq204 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq191 eq16
    | exact resolve eq16 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq831 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq885 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq885 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq885 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq885 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq930 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq886 X0
       grind)
    | exact superpose eq886 eq194
    | exact resolve eq194 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq935 : (M.op x y) = (M.op (k y y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq201 y
       have i₂ := eq886 y
       grind)
    | exact superpose eq886 eq201
    | exact resolve eq201 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq937 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq204 sF3
       have i₂ := eq886 sF3
       grind)
    | exact superpose eq886 eq204
    | exact resolve eq204 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq939 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0
       have i₂ := eq886 (M.op X0 X0)
       grind)
    | exact superpose eq886 eq180
    | exact resolve eq180 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq946 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq939 X0
       have i₂ := eq886 X0
       grind)
    | exact superpose eq886 eq939
    | exact resolve eq939 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq948 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq937
       have i₂ := eq886 sF4
       grind)
    | exact superpose eq886 eq937
    | exact resolve eq937 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq950 : (M.op x y) = (M.op (k y y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq935
       have i₂ := eq886 sF0
       grind)
    | exact superpose eq886 eq935
    | exact resolve eq935 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1285 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq948 eq16
    | exact resolve eq16 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1286 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1285 X0
       have i₂ := eq886 (k sF3 sF3)
       grind)
    | exact superpose eq886 eq1285
    | exact resolve eq1285 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1292 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1286 X0
       have i₂ := eq946 sF3
       grind)
    | exact superpose eq946 eq1286
    | exact resolve eq1286 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1307 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (M.op (k y y) (k y y))) := by
    intro X0
    first
    | exact superpose eq950 eq16
    | exact resolve eq16 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1308 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) (k (k y y) (k y y))) := by
    intro X0
    first
    | (have i₁ := eq1307 X0
       have i₂ := eq886 (k y y)
       grind)
    | exact superpose eq886 eq1307
    | exact resolve eq1307 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1313 : ∀ X0 : G, (k y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq1308 X0
       have i₂ := eq946 y
       grind)
    | exact superpose eq946 eq1308
    | exact resolve eq1308 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1324 : (k (σ y) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1292 (k sF4 sF4)
       have i₂ := eq930 sF4
       grind)
    | exact superpose eq930 eq1292
    | exact resolve eq1292 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1347 : (k y y) = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq1313 (k sF0 sF0)
       have i₂ := eq930 sF0
       grind)
    | exact superpose eq930 eq1313
    | exact resolve eq1313 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq1313
  have eq1401 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq40
    | exact resolve eq40 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1402 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1401
    | exact resolve eq1401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1404 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq1402
    | exact resolve eq1402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1406 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1404
       have i₂ := eq886 x
       grind)
    | exact superpose eq886 eq1404
    | exact resolve eq1404 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1406 eq833
    | exact resolve eq833 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1424 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1417
       have r₂ := eq27
       grind)
    | exact resolve eq1417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1428 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1424
       have i₂ := eq886 sF2
       grind)
    | exact superpose eq886 eq1424
    | exact resolve eq1424 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1437 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1428 eq946
    | exact resolve eq946 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1444 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1437 eq1324
    | exact resolve eq1324 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1452 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq26 eq1444
    | exact resolve eq1444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1444
  have eq1514 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1452 eq946
    | exact resolve eq946 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1517 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1437 eq1514
    | exact resolve eq1514 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq1514
  have eq1528 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq946 x
       have i₂ := eq1517
       grind)
    | exact superpose eq1517 eq946
    | exact resolve eq946 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1554 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1528 eq1347
    | exact resolve eq1347 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1566 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1554
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1554
    | exact resolve eq1554 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1554
  have eq1612 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq946 y
       have i₂ := eq1566
       grind)
    | exact superpose eq1566 eq946
    | exact resolve eq946 eq1566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq1566
  have eq1615 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1528 eq1612
    | exact resolve eq1612 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528 eq1612
  have eq1623 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1615 eq32
    | exact resolve eq32 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1615
  have eq1662 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1623
    | exact resolve eq1623 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1623
  have eq1663 : x = y := by grind
  clear eq1662
  have eq1666 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1663
       grind)
    | exact superpose eq1663 eq24
    | exact resolve eq24 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1671 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq831
       have i₂ := eq1663
       grind)
    | exact superpose eq1663 eq831
    | exact resolve eq831 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq1663
  have eq1678 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1671
       have i₂ := eq886 x
       grind)
    | exact superpose eq886 eq1671
    | exact resolve eq1671 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq1679 : (M.op x y) = (k x x) := by grind
  clear eq1678
  have eq1684 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1666
    | exact resolve eq1666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1702 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1684 eq833
    | exact resolve eq833 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq1684
  have eq1710 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1702
       have i₂ := eq886 sF2
       grind)
    | exact superpose eq886 eq1702
    | exact resolve eq1702 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq1702
  have eq1711 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1710
  have eq1732 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1679
       grind)
    | exact superpose eq1679 eq40
    | exact resolve eq40 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1679
  have eq1737 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1732
    | exact resolve eq1732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1732
  have eq1740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1711 eq1737
    | exact resolve eq1737 eq1711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711 eq1737
  have eq1742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1740
    | exact resolve eq1740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1740
  have eq1744 : False := by grind
  exact eq1744

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq42 X0 X2
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op X0 X0)
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq40
    | exact resolve eq40 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1 (M.op X0 X0)
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq50
    | exact resolve eq50 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq49 X0
       grind)
    | exact resolve eq13 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq112 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq110
    | (have j0 := eq110 X0
       grind)
    | exact resolve eq110 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq274 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq48 X1 X1 X0
       grind)
    | exact superpose eq48 eq50
    | exact resolve eq50 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq334 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq334 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq334
    | (have j0 := eq334 (σ X0) (σ X1)
       grind)
    | exact resolve eq334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq334 (τ X0) X1
       grind)
    | exact superpose eq334 eq17
    | (have j1 := eq334 (τ X0) X1
       grind)
    | exact resolve eq17 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X1 (M.op X0 X2))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 (M.op X1 (M.op X0 X2)) (M.op X0 X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq87
    | exact resolve eq87 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48 X2 X3 X1
       have i₂ := eq87 X1 X2 X0
       grind)
    | (have i₁ := eq48 X1 X1 X1
       have i₂ := eq87 X1 X1 X1
       grind)
    | exact superpose eq87 eq48
    | exact resolve eq48 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq540 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 (M.op X0 X1) X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq9 (M.op X0 X1) x x
       grind)
    | exact superpose eq9 eq414
    | exact resolve eq414 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq87 (M.op X3 (M.op X1 (M.op X0 X2))) X0 X2
       have i₂ := eq414 X0 X1 X2 X3
       grind)
    | exact superpose eq414 eq87
    | exact resolve eq87 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq560 X0 X1 X2 X3 X4
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq560
    | exact resolve eq560 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq579 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq540
    | exact resolve eq540 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1493 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337 x y
       grind)
    | exact superpose eq337 eq16
    | (have j1 := eq337 x y
       grind)
    | exact resolve eq16 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1518 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq337 X0 X0
       grind)
    | exact superpose eq337 eq9
    | (have j1 := eq337 X0 X0
       grind)
    | exact resolve eq9 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (σ X0)
       have i₂ := eq337 X0 X0
       grind)
    | exact superpose eq337 eq40
    | (have j1 := eq337 (k X0 X0) X0
       grind)
    | exact resolve eq40 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq337 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq1542 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1529 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1529
    | (have j0 := eq1529 (τ X0)
       grind)
    | exact resolve eq1529 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1542 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1542
    | (have j0 := eq1542 X0
       grind)
    | exact resolve eq1542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1546 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1543 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1543
    | (have j0 := eq1543 X0
       grind)
    | exact resolve eq1543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1552 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1546 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1546
    | (have j0 := eq1546 (τ X0)
       grind)
    | exact resolve eq1546 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1546
  have eq1674 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X2 X0)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq414 (M.op X2 X0) (M.op x X1) (M.op X0 X1) X3
       have i₂ := eq422 X2 X0 X1 x
       grind)
    | exact superpose eq422 eq414
    | exact resolve eq414 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq1676 : ∀ X0 X1 X3 : G, (M.op X3 X0) = (M.op (M.op X0 X1) (M.op (M.op X3 X0) (M.op X3 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) (M.op x X1) (M.op X0 X1)
       have i₂ := eq422 X3 X0 X1 x
       grind)
    | exact superpose eq422 eq9
    | exact resolve eq9 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq1715 : ∀ X0 X1 X3 : G, (M.op X3 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X3 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1676 X0 X1 X3
       have i₂ := eq579 X0 X3
       grind)
    | exact superpose eq579 eq1676
    | exact resolve eq1676 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq1716 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1674 X0 X1 X2 X3
       have i₂ := eq579 X0 X2
       grind)
    | exact superpose eq579 eq1674
    | exact resolve eq1674 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1771 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1715 X0 (M.op X0 X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq1715
    | exact resolve eq1715 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq3073 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (M.op X0 X0) X1 (M.op x (M.op x (M.op x (M.op X0 x))))
       have i₂ := eq570 X0 x x x x
       grind)
    | exact superpose eq570 eq87
    | exact resolve eq87 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq570
  have eq3121 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3073 X0 X1
       have i₂ := eq579 X1 (M.op X0 X0)
       grind)
    | exact superpose eq579 eq3073
    | exact resolve eq3073 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq3073
  have eq3791 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361
    | exact resolve eq361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq3821 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3791 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3791
    | (have j0 := eq3791 X0 X1
       grind)
    | exact resolve eq3791 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3851 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 X1) X2
       have i₂ := eq3821 X0 X1
       grind)
    | exact superpose eq3821 eq28
    | (have j1 := eq3821 X0 X1
       grind)
    | exact resolve eq28 eq3821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3851 X0 X1 X2
       have i₂ := eq28 (M.op X0 X1) X2
       grind)
    | exact superpose eq28 eq3851
    | (have j0 := eq3851 X0 X1 X2
       grind)
    | exact resolve eq3851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3851
  have eq5023 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1771 X1 (M.op X0 X0)
       have i₂ := eq3121 X0 X1
       grind)
    | (have i₁ := eq1771 X1 (M.op X1 X1)
       have i₂ := eq3121 X1 X1
       grind)
    | exact superpose eq3121 eq1771
    | exact resolve eq1771 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq3121
  have eq5245 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1716 X0 (M.op (M.op X0 X0) X1) X2 X1
       have i₂ := eq5023 X0 X1
       grind)
    | exact superpose eq5023 eq1716
    | exact resolve eq1716 eq5023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716 eq5023
  have eq5439 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq334 x y
       grind)
    | exact superpose eq334 eq1493
    | (have j1 := eq334 (σ x) (σ y)
       grind)
    | exact resolve eq1493 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq5442 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq5439
  have eq5455 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq5442
       grind)
    | exact superpose eq5442 eq88
    | exact resolve eq88 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6688 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1520 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1520
    | (have j0 := eq1520 (τ X0)
       grind)
    | exact resolve eq1520 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq6759 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6688 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6688
    | (have j0 := eq6688 X0
       grind)
    | exact resolve eq6688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6688
  have eq6763 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6759 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6759
    | (have j0 := eq6759 X0
       grind)
    | exact resolve eq6759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6759
  have eq6772 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq6763 X0
       grind)
    | exact superpose eq6763 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq6763 X0
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq6763 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq6763 X0
       grind)
    | exact resolve eq13 eq6763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq6830 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq6772 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6772
  have eq6831 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830
  have eq7109 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (σ (τ X0)) X2)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1518 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1518
    | (have j0 := eq1518 (τ X0) X1 X2
       grind)
    | exact resolve eq1518 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1518
  have eq7203 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7109 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7109
    | (have j0 := eq7109 X0 X1 X2
       grind)
    | exact resolve eq7109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7109
  have eq7208 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7203 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7203
    | (have j0 := eq7203 X0 X1 X2
       grind)
    | exact resolve eq7203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq8167 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7208 X0 x (k X0 X0)
       have i₂ := eq274 X0 (k X0 X0) x
       grind)
    | exact superpose eq274 eq7208
    | (have j0 := eq7208 X0 x x
       grind)
    | exact resolve eq7208 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq7208
  have eq8491 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k X0 X0) X1
       have i₂ := eq8167 X0
       grind)
    | exact superpose eq8167 eq42
    | (have j1 := eq8167 X0
       grind)
    | exact resolve eq42 eq8167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8167
  have eq11205 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5442
       have i₂ := eq5455
       grind)
    | exact superpose eq5455 eq5442
    | exact resolve eq5442 eq5455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5455
  have eq11269 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq11205
  have eq11289 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 (σ x)
       have i₂ := eq11269
       grind)
    | exact superpose eq11269 eq40
    | exact resolve eq40 eq11269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11296 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq112 (σ x)
       have i₂ := eq11269
       grind)
    | exact superpose eq11269 eq112
    | exact resolve eq112 eq11269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11269
  have eq11390 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11296
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq11296
    | exact resolve eq11296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11296
  have eq11396 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11289
       grind)
    | exact superpose eq11289 eq16
    | exact resolve eq16 eq11289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289
  have eq28708 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3821 x y
       have i₂ := eq11390
       grind)
    | exact superpose eq11390 eq3821
    | (have j0 := eq3821 x y
       grind)
    | exact resolve eq3821 eq11390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821 eq11390
  have eq28734 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq28708
  have eq28751 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28734
       have r₂ := eq11396
       grind)
    | exact resolve eq28734 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396 eq28734
  have eq28761 : (M.op y x) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq28751
       grind)
    | exact superpose eq28751 eq88
    | exact resolve eq88 eq28751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28826 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x x) X0) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5245 x x y
       have i₂ := eq28751
       grind)
    | exact superpose eq28751 eq5245
    | exact resolve eq5245 eq28751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq29173 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28751
       have i₂ := eq28761
       grind)
    | exact superpose eq28761 eq28751
    | exact resolve eq28751 eq28761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28751 eq28761
  have eq29261 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq29173
  have eq29281 : ∀ X0 : G, x ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq79 x x
       have i₂ := eq29261
       grind)
    | exact superpose eq29261 eq79
    | exact resolve eq79 eq29261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29316 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42 x x
       have i₂ := eq29261
       grind)
    | exact superpose eq29261 eq42
    | exact resolve eq42 eq29261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq29261
  have eq52337 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28826 (k y y)
       have i₂ := eq8491 y (M.op x x)
       grind)
    | exact superpose eq8491 eq28826
    | (have j1 := eq8491 y x
       grind)
    | exact resolve eq28826 eq8491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8491 eq28826
  have eq255856 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3854 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3854
    | (have j0 := eq3854 X1 X2 X2
       grind)
    | exact resolve eq3854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq256276 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6831 X0
       have i₂ := eq255856 X0 X0 X0
       grind)
    | exact superpose eq255856 eq6831
    | (have j0 := eq6831 X0
       have j1 := eq255856 X0 X0 X0
       grind)
    | exact resolve eq6831 eq255856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6831 eq255856
  have eq256575 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq256276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256276
  have eq256648 : (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq256575 y
       have i₂ := eq29316
       grind)
    | exact superpose eq29316 eq256575
    | exact resolve eq256575 eq29316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29316 eq256575
  have eq257683 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52337
       have i₂ := eq256648
       grind)
    | exact superpose eq256648 eq52337
    | exact resolve eq52337 eq256648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52337 eq256648
  have eq257856 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq257683
  have eq257931 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq257856
       have r₂ := eq12 x y
       grind)
    | exact resolve eq257856 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257856
  have eq257939 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq29281 x
       grind)
    | (have r₁ := eq257931
       have r₂ := eq29281 x
       grind)
    | exact resolve eq257931 eq29281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29281 eq257931
  have eq257946 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq257939
       grind)
    | exact superpose eq257939 eq1493
    | exact resolve eq1493 eq257939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq258008 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq257946
  have eq259911 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88 (σ x) (σ y)
       have i₂ := eq258008
       grind)
    | exact superpose eq258008 eq88
    | exact resolve eq88 eq258008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq266524 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq258008
       have i₂ := eq259911
       grind)
    | exact superpose eq259911 eq258008
    | exact resolve eq258008 eq259911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258008 eq259911
  have eq266733 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq266524
  have eq266829 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 (σ x)
       have i₂ := eq266733
       grind)
    | exact superpose eq266733 eq40
    | exact resolve eq40 eq266733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq266836 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112 (σ x)
       have i₂ := eq266733
       grind)
    | exact superpose eq266733 eq112
    | exact resolve eq112 eq266733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq266733
  have eq267087 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq266836
  have eq267179 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq267087
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq267087
    | exact resolve eq267087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267087
  have eq268092 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq267179
       have i₂ := eq257939
       grind)
    | exact superpose eq257939 eq267179
    | exact resolve eq267179 eq257939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257939 eq267179
  have eq268363 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq268092
  have eq269852 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq266829
       grind)
    | exact superpose eq266829 eq16
    | exact resolve eq16 eq266829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266829
  have eq270102 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq269852
       have r₂ := eq268363
       grind)
    | exact resolve eq269852 eq268363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268363 eq269852
  have eq270105 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5442
       have i₂ := eq270102
       grind)
    | exact superpose eq270102 eq5442
    | exact resolve eq5442 eq270102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442
  have eq270120 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq270102
       grind)
    | exact superpose eq270102 eq10
    | exact resolve eq10 eq270102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270102
  have eq270365 : x = y := by
    first
    | (have i₁ := eq270120
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq270120
    | exact resolve eq270120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270120
  have eq270380 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270365
       grind)
    | exact superpose eq270365 eq16
    | exact resolve eq16 eq270365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270416 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq270105
       have i₂ := eq270365
       grind)
    | exact superpose eq270365 eq270105
    | exact resolve eq270105 eq270365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270105 eq270365
  have eq270469 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq79 (σ x) x
       have i₂ := eq270416
       grind)
    | exact superpose eq270416 eq79
    | (have r₁ := eq79 (σ x) x
       have r₂ := eq270416
       grind)
    | (have r₁ := eq79 x x
       have r₂ := eq270416
       grind)
    | exact resolve eq79 eq270416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270660 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq270469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270469
  have eq272501 : (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1552 (σ x)
       have i₂ := eq270660 (σ x)
       grind)
    | exact superpose eq270660 eq1552
    | (have j0 := eq1552 (σ x)
       grind)
    | exact resolve eq1552 eq270660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq270660
  have eq272813 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272501
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq272501
    | exact resolve eq272501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272501
  have eq272832 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272813
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq272813
    | exact resolve eq272813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272813
  have eq272833 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq272832
  have eq272844 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272833
       have i₂ := eq270416
       grind)
    | exact superpose eq270416 eq272833
    | exact resolve eq272833 eq270416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270416 eq272833
  have eq272854 : x ≠ (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq272844
  have eq272856 : x = (M.op x x) := by
    first
    | (have r₁ := eq272854
       have r₂ := eq10 x
       grind)
    | exact resolve eq272854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272854
  have eq272929 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq79 x x
       have i₂ := eq272856
       grind)
    | exact superpose eq272856 eq79
    | (have r₁ := eq79 x x
       have r₂ := eq272856
       grind)
    | exact resolve eq79 eq272856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq273119 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq272929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272929
  have eq273217 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1529 x
       have i₂ := eq273119 x
       grind)
    | exact superpose eq273119 eq1529
    | (have j0 := eq1529 x
       grind)
    | exact resolve eq1529 eq273119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq273119
  have eq273561 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq273217
       have i₂ := eq272856
       grind)
    | exact superpose eq272856 eq273217
    | exact resolve eq273217 eq272856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273217
  have eq273562 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq273561
  have eq273887 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq270380
       have i₂ := eq273562
       grind)
    | exact superpose eq273562 eq270380
    | exact resolve eq270380 eq273562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270380 eq273562
  have eq274195 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq273887
       have i₂ := eq272856
       grind)
    | exact superpose eq272856 eq273887
    | exact resolve eq273887 eq272856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272856 eq273887
  have eq274196 : False := by grind
  exact eq274196

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq54
    | (have j0 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq54 (τ X1) X0
       grind)
    | exact superpose eq54 eq17
    | (have j1 := eq54 (τ X1) X0
       grind)
    | exact resolve eq17 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq75 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq158 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq222 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq239 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq245 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq239 X0 X0
       grind)
    | exact superpose eq239 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq239 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq239 X0 X0
       grind)
    | exact resolve eq12 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq245 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq307 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq98
    | (have j1 := eq54 (σ y) (σ x)
       grind)
    | exact resolve eq98 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq98
  have eq308 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq307
  have eq323 : y = (M.op x (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75 y x
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq75
    | exact resolve eq75 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (M.op X0 X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq24
    | exact resolve eq24 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X0 X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq158
    | exact resolve eq158 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq158
  have eq2355 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq614 y x
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq614
    | exact resolve eq614 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2577 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq323
       have i₂ := eq2355
       grind)
    | exact superpose eq2355 eq323
    | exact resolve eq323 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq2355
  have eq2606 : y = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2577
  have eq2812 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2606
       have i₂ := eq308
       grind)
    | exact superpose eq308 eq2606
    | exact resolve eq2606 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq2606
  have eq2843 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2812
  have eq5287 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq259 X0 X1
       grind)
    | exact superpose eq259 eq10
    | (have j1 := eq259 X0 X1
       grind)
    | exact resolve eq10 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq5347 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5287 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5287
    | (have j0 := eq5287 X0 X0
       grind)
    | exact resolve eq5287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5287
  have eq5561 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5347 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5347
  have eq5562 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5561
  have eq5738 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5562 (σ X0)
       grind)
    | exact superpose eq5562 eq15
    | exact resolve eq15 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5782 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5738 X0
       have i₂ := eq5562 X0
       grind)
    | exact superpose eq5562 eq5738
    | exact resolve eq5738 eq5562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5562 eq5738
  have eq6296 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq5782 X0
       grind)
    | exact superpose eq5782 eq24
    | exact resolve eq24 eq5782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq7436 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6296 x
       have i₂ := eq2843
       grind)
    | exact superpose eq2843 eq6296
    | exact resolve eq6296 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843 eq6296
  have eq7474 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7436
  have eq7579 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7474
       grind)
    | exact superpose eq7474 eq16
    | exact resolve eq16 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7596 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq614 (σ y) (σ x)
       have i₂ := eq7474
       grind)
    | exact superpose eq7474 eq614
    | exact resolve eq614 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq7605 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7596
       have i₂ := eq5782 y
       grind)
    | exact superpose eq5782 eq7596
    | exact resolve eq7596 eq5782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782 eq7596
  have eq7612 : (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7605
       have i₂ := eq7474
       grind)
    | exact superpose eq7474 eq7605
    | exact resolve eq7605 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474 eq7605
  have eq7865 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7612
       grind)
    | exact superpose eq7612 eq10
    | exact resolve eq10 eq7612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7612
  have eq7940 : x = (M.op y y) := by
    first
    | (have i₁ := eq7865
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7865
    | exact resolve eq7865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7865
  have eq8142 : x = (M.op x y) := by
    first
    | (have i₁ := eq334 y
       have i₂ := eq7940
       grind)
    | exact superpose eq7940 eq334
    | exact resolve eq334 eq7940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq7940
  have eq8371 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7579
       have i₂ := eq8142
       grind)
    | exact superpose eq8142 eq7579
    | exact resolve eq7579 eq8142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579 eq8142
  have eq8395 : False := by grind
  exact eq8395

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq79 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op y x) := by
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
  have eq89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq97
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq101
  have eq406 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq704 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2595 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (M.op X0 X0) X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq406
    | exact resolve eq406 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq3865 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2595 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2595
    | (have j0 := eq2595 y X0
       grind)
    | exact resolve eq2595 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq3882 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3865 X0
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq3865
    | exact resolve eq3865 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq3865
  have eq4136 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3882
    | (have j0 := eq3882 (σ x)
       grind)
    | exact resolve eq3882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq4149 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq4136 eq14
    | exact resolve eq14 eq4136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4226 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X0 X1
       have i₂ := eq58 X0 X0
       grind)
    | exact superpose eq58 eq704
    | exact resolve eq704 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq4279 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4226 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4226
    | (have j0 := eq4226 y x
       grind)
    | exact resolve eq4226 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4347 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op y y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4279 eq14
    | exact resolve eq14 eq4279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4355 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq4347 y
       have i₂ := eq56 y
       grind)
    | exact superpose eq56 eq4347
    | exact resolve eq4347 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq5006 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4149 sF3
       have i₂ := eq56 sF3
       grind)
    | exact superpose eq56 eq4149
    | exact resolve eq4149 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4149
  have eq15286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq15286
    | exact resolve eq15286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq15298 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq15287
       have r₂ := eq28
       grind)
    | exact resolve eq15287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15287
  have eq15302 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq15298
    | exact resolve eq15298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq15306 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15302 eq89
    | (have r₁ := eq89
       have r₂ := eq15302
       grind)
    | exact resolve eq89 eq15302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq15342 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15302 eq58
    | exact resolve eq58 eq15302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15302
  have eq15354 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15306
  have eq15355 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15354
  have eq15525 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15342 eq5006
    | exact resolve eq5006 eq15342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5006 eq15342
  have eq16450 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15355 eq75
    | exact resolve eq75 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq15355
  have eq16464 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16450
  have eq16470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16464 eq15525
    | exact resolve eq15525 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15525 eq16464
  have eq16493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq16470
  have eq16495 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16493
       have r₂ := eq28
       grind)
    | exact resolve eq16493 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16493
  have eq16631 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq16495
       grind)
    | exact superpose eq16495 eq52
    | exact resolve eq52 eq16495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq16634 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq16495
       grind)
    | exact superpose eq16495 eq88
    | (have r₁ := eq88
       have r₂ := eq16495
       grind)
    | exact resolve eq88 eq16495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq16668 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq58 x x
       have i₂ := eq16495
       grind)
    | exact superpose eq16495 eq58
    | exact resolve eq58 eq16495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq16495
  have eq16680 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq16634
  have eq16681 : (k x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16680
  have eq16703 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16631
    | exact resolve eq16631 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16631
  have eq16886 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16668 eq4355
    | exact resolve eq4355 eq16668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355 eq16668
  have eq17969 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq16681
       grind)
    | exact superpose eq16681 eq49
    | exact resolve eq49 eq16681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq16681
  have eq20064 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17969
       have i₂ := eq16886
       grind)
    | exact superpose eq16886 eq17969
    | exact resolve eq17969 eq16886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16886 eq17969
  have eq20128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20064
  have eq20135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq20128
    | exact resolve eq20128 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20128
  have eq20153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20135
  have eq20154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20153
  have eq20158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq20154
    | exact resolve eq20154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20154
  have eq20170 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20158
       have r₂ := eq28
       grind)
    | exact resolve eq20158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20158
  have eq20174 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq20170
    | exact resolve eq20170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20170
  have eq20420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20174 eq16703
    | exact resolve eq16703 eq20174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16703 eq20174
  have eq20468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20420
  have eq20482 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20468
       have r₂ := eq28
       grind)
    | exact resolve eq20468 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20468
  have eq20486 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20482 eq30
    | exact resolve eq30 eq20482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20482
  have eq20612 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq20486
    | exact resolve eq20486 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20486
  have eq20613 : x = y := by grind
  clear eq20612
  have eq20632 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20613
       grind)
    | exact superpose eq20613 eq19
    | exact resolve eq19 eq20613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20633 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20613
       grind)
    | exact superpose eq20613 eq25
    | exact resolve eq25 eq20613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20613
  have eq20747 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20633
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20633
    | exact resolve eq20633 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20633
  have eq20964 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20747 eq27
    | exact resolve eq27 eq20747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20747
  have eq21230 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20964 eq79
    | exact resolve eq79 eq20964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq20964
  have eq21302 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21230
       have i₂ := eq20632
       grind)
    | exact superpose eq20632 eq21230
    | exact resolve eq21230 eq20632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20632 eq21230
  have eq21319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21302 eq15
    | exact resolve eq15 eq21302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21302
  have eq21378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21319
    | exact resolve eq21319 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21319
  have eq21390 : False := by grind
  exact eq21390
