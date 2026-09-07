import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1315 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1336 : False := by grind
  exact eq1336

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation422 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq91 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq91 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq13
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq111
    | exact resolve eq111 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq111
  have eq1034 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have r₁ := eq14
       have r₂ := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1058 : False := by grind
  exact eq1058

/-- `Equation4268`: `x ◇ (x ◇ x) = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4268 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4268 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4268.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 X1 X1
       have i₂ := eq8 X1 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq136 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq142 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq18 X0 X2 X1
       grind)
    | (have i₁ := eq81 X0 (M.op X0 X2)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq81
    | (have j0 := eq81 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq18 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq81 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq18 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq207 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq31 X0 X2
       grind)
    | exact superpose eq31 eq13
    | (have j1 := eq31 X0 X2
       grind)
    | exact resolve eq13 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq475 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq528 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq475 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq475
    | (have j0 := eq475 X0 X1
       grind)
    | exact resolve eq475 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207
       have i₂ := eq528 y x
       grind)
    | exact superpose eq528 eq207
    | (have j1 := eq528 (σ y) (σ x)
       grind)
    | (have r₁ := eq207
       have r₂ := eq528 y x
       grind)
    | exact resolve eq207 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1084 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1083
  have eq1123 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 X1 X2
       have i₂ := eq217 X1 X0
       grind)
    | (have i₁ := eq217 X0 X1
       have i₂ := eq217 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq217 eq217
    | (have j0 := eq217 X1 X2
       have j1 := eq217 X1 X2
       grind)
    | exact resolve eq217 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq217 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq217
    | exact resolve eq217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (σ X0) (σ X1) X2
       have i₂ := eq217 X0 X1
       grind)
    | exact superpose eq217 eq18
    | (have j1 := eq217 X0 X1
       grind)
    | exact resolve eq18 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1174 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1130
    | (have j0 := eq1130 X0 X1
       grind)
    | exact resolve eq1130 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1130
  have eq2868 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq136 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq4309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq219
  have eq5181 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1174 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1174
    | (have j0 := eq1174 X1 (τ X0)
       grind)
    | exact resolve eq1174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq14599 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq31861 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4309 (τ X1) (τ X0)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq4309
    | exact resolve eq4309 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32179 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4309 x x
       have i₂ := eq1084
       grind)
    | exact superpose eq1084 eq4309
    | exact resolve eq4309 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq32444 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4309 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq32445 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq32444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32444
  have eq32452 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq32179
  have eq32870 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31861 X0 X1
       have i₂ := eq32445 (τ X0)
       grind)
    | exact superpose eq32445 eq31861
    | (have j0 := eq31861 X0 X1
       grind)
    | exact resolve eq31861 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31861
  have eq33130 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32870 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq32870
    | (have j0 := eq32870 X0 X1
       grind)
    | exact resolve eq32870 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32870
  have eq33271 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33130 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33130
    | (have j0 := eq33130 X0 X1
       grind)
    | exact resolve eq33130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33130
  have eq33346 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33271 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33271
    | (have j0 := eq33271 X0 X1
       grind)
    | exact resolve eq33271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33271
  have eq33384 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33346 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33346
    | (have j0 := eq33346 X0 X1
       grind)
    | exact resolve eq33346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33346
  have eq33402 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33384 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33384
    | (have j0 := eq33384 X0 X1
       grind)
    | exact resolve eq33384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33384
  have eq33407 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33402 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33402
    | (have j0 := eq33402 X0 X1
       grind)
    | exact resolve eq33402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33402
  have eq33441 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32445 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32445
    | exact resolve eq32445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33548 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 X1 (σ X0)
       have i₂ := eq32445 X0
       grind)
    | exact superpose eq32445 eq5181
    | (have j0 := eq5181 X1 (σ X0)
       grind)
    | exact resolve eq5181 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq33557 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) X1 (σ X0)
       have i₂ := eq32445 X0
       grind)
    | exact superpose eq32445 eq18
    | exact resolve eq18 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33574 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33548 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq33548
    | (have j0 := eq33548 X0 X1
       grind)
    | exact resolve eq33548 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33548
  have eq33620 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq33441 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq33441
    | exact resolve eq33441 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq33441
  have eq33645 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq33620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33620
    | exact resolve eq33620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33620
  have eq42839 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq32452
       grind)
    | exact superpose eq32452 eq9
    | exact resolve eq9 eq32452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32452
  have eq43071 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq42839
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq42839
    | exact resolve eq42839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42839
  have eq43157 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43071
       have i₂ := eq33645 x
       grind)
    | exact superpose eq33645 eq43071
    | exact resolve eq43071 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43071
  have eq43158 : y = (M.op x x) := by grind
  clear eq43157
  have eq43954 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq18 x X0 x
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq18
    | exact resolve eq18 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq43959 : (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq14599 x x
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq14599
    | exact resolve eq14599 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55269 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33645 X0
       have i₂ := eq33407 X0 X1
       grind)
    | (have i₁ := eq33645 X1
       have i₂ := eq33407 X1 X1
       grind)
    | exact superpose eq33407 eq33645
    | (have j1 := eq33407 X0 X1
       grind)
    | exact resolve eq33645 eq33407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55385 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55386 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33407
  have eq55387 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55386 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55386
    | (have j0 := eq55386 X0 X1
       grind)
    | (have r₁ := eq55386 X0 X0
       have r₂ := eq33645 X0
       grind)
    | exact resolve eq55386 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55386
  have eq55388 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55385 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55385
    | (have j0 := eq55385 X0 X1
       grind)
    | (have r₁ := eq55385 X0 X0
       have r₂ := eq33645 X0
       grind)
    | exact resolve eq55385 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55385
  have eq55753 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55388 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq55388
    | (have j0 := eq55388 X0 X1
       grind)
    | exact resolve eq55388 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55388
  have eq58976 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq55753 x (M.op x X0)
       have i₂ := eq43954 X0
       grind)
    | exact superpose eq43954 eq55753
    | (have j0 := eq55753 x y
       grind)
    | exact resolve eq55753 eq43954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55753
  have eq59027 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq58976 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq58976
    | (have j0 := eq58976 X0
       grind)
    | exact resolve eq58976 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58976
  have eq59095 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq59027 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq59027
    | exact resolve eq59027 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59027
  have eq87198 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (M.op (σ (τ X0)) X2)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2868 (τ X1) (τ X0) X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq2868
    | exact resolve eq2868 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2868
  have eq87581 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87198 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87198
    | (have j0 := eq87198 X0 X1 X2
       grind)
    | exact resolve eq87198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87198
  have eq87698 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87581 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq87581
    | (have j0 := eq87581 X0 X1 X2
       grind)
    | exact resolve eq87581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87581
  have eq87762 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87698 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq87698
    | (have j0 := eq87698 X0 X1 X2
       grind)
    | exact resolve eq87698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87698
  have eq87803 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87762 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87762
    | (have j0 := eq87762 X0 X1 X2
       grind)
    | exact resolve eq87762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87762
  have eq87826 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87803 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq87803
    | (have j0 := eq87803 X0 X1 X2
       grind)
    | exact resolve eq87803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87803
  have eq88073 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33557 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq33557
    | exact resolve eq33557 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33557
  have eq89872 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33574 X0 (σ X1)
       grind)
    | exact superpose eq33574 eq9
    | (have j1 := eq33574 X0 (σ X1)
       grind)
    | exact resolve eq9 eq33574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33574
  have eq90382 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89872 X0 X1
       have i₂ := eq33645 X0
       grind)
    | exact superpose eq33645 eq89872
    | (have j0 := eq89872 X0 X1
       grind)
    | exact resolve eq89872 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89872
  have eq90770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90382 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq90382
    | (have j0 := eq90382 X0 X1
       grind)
    | exact resolve eq90382 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90382
  have eq119392 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq88073 x X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq88073
    | exact resolve eq88073 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88073
  have eq124259 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14599 (σ x) x
       have i₂ := eq119392 x
       grind)
    | exact superpose eq119392 eq14599
    | exact resolve eq14599 eq119392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14599
  have eq128405 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq39 x (M.op (σ x) (σ y))
       have i₂ := eq124259
       grind)
    | exact superpose eq124259 eq39
    | exact resolve eq39 eq124259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq130711 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X1 X2)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq528 X2 X1
       have i₂ := eq90770 X1 X0
       grind)
    | (have i₁ := eq528 X0 X1
       have i₂ := eq90770 X0 (M.op X1 X1)
       grind)
    | exact superpose eq90770 eq528
    | (have j0 := eq528 X2 X1
       have j1 := eq90770 X1 X0
       grind)
    | exact resolve eq528 eq90770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq90770
  have eq139518 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq1123 y x X0
       grind)
    | exact superpose eq1123 eq14
    | (have j1 := eq1123 y x X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq1123 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq1123 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq139730 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq139518 X0
       have j1 := eq130711 (σ (k x X0)) x (M.op (σ x) (σ X0))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 (σ (M.op x y)) x (σ (k x y))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 (σ (k x y)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq139518 X0
       have r₂ := eq130711 X0 x y
       grind)
    | exact resolve eq139518 eq130711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130711 eq139518
  have eq141277 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1167 x (M.op x y) X0
       have i₂ := eq43959
       grind)
    | exact superpose eq43959 eq1167
    | (have j0 := eq1167 x (M.op x y) x
       grind)
    | exact resolve eq1167 eq43959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq141724 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq141277 x
       have i₂ := eq119392 x
       grind)
    | exact superpose eq119392 eq141277
    | exact resolve eq141277 eq119392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119392 eq141277
  have eq142099 : (M.op x y) = (τ (σ (k x x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141724
       have i₂ := eq32445 x
       grind)
    | exact superpose eq32445 eq141724
    | exact resolve eq141724 eq32445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32445 eq141724
  have eq142437 : (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142099
       have i₂ := eq9 (k x x)
       grind)
    | exact superpose eq9 eq142099
    | exact resolve eq142099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142099
  have eq142704 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142437
       have i₂ := eq33645 x
       grind)
    | exact superpose eq33645 eq142437
    | exact resolve eq142437 eq33645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33645 eq142437
  have eq142881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq142704
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq142704
    | exact resolve eq142704 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142704
  have eq205683 : ∀ X0 : G, (M.op x y) ≠ (k x X0) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq87826 x X0 x
       have i₂ := eq43954 x
       grind)
    | exact superpose eq43954 eq87826
    | (have j0 := eq87826 x X0 x
       grind)
    | exact resolve eq87826 eq43954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43954 eq87826
  have eq206881 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x X0) = (M.op x x) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq205683 x
       have i₂ := eq55269 x x
       grind)
    | exact superpose eq55269 eq205683
    | (have j0 := eq205683 X0
       have j1 := eq55269 x X0
       grind)
    | (have r₁ := eq205683 y
       have r₂ := eq55269 x y
       grind)
    | exact resolve eq205683 eq55269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55269 eq205683
  have eq206913 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq206881 X0
       have j1 := eq55387 x y
       grind)
    | (have r₁ := eq206881 x
       have r₂ := eq55387 x x
       grind)
    | (have r₁ := eq206881 x
       have r₂ := eq55387 x x
       grind)
    | exact resolve eq206881 eq55387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55387 eq206881
  have eq206925 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq206913 X0
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq206913
    | (have j0 := eq206913 X0
       grind)
    | exact resolve eq206913 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206913
  have eq1132494 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq139730 (M.op x y)
       have i₂ := eq142881
       grind)
    | exact superpose eq142881 eq139730
    | (have j0 := eq139730 (M.op x y)
       grind)
    | exact resolve eq139730 eq142881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139730 eq142881
  have eq1132504 : (M.op (σ x) (σ y)) = (σ (k x (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq1132494
  have eq1132507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1132504
       have i₂ := eq43959
       grind)
    | exact superpose eq43959 eq1132504
    | exact resolve eq1132504 eq43959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43959 eq1132504
  have eq1132509 : y = (M.op x y) := by
    first
    | (have r₁ := eq1132507
       have r₂ := eq14
       grind)
    | exact resolve eq1132507 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132507
  have eq1132532 : ∀ X0 : G, y ≠ y ∨ y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq59095 X0
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq59095
    | (have j0 := eq59095 X0
       grind)
    | (have r₁ := eq59095 X0
       have r₂ := eq1132509
       grind)
    | exact resolve eq59095 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59095
  have eq1132539 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq206925 X0
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq206925
    | (have j0 := eq206925 X0
       grind)
    | (have r₁ := eq206925 X0
       have r₂ := eq1132509
       grind)
    | exact resolve eq206925 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206925
  have eq1132598 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq1132539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132539
  have eq1132605 : ∀ X0 : G, y = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq1132532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132532
  have eq1132627 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1132605 X0
       have i₂ := eq1132598 (M.op x X0)
       grind)
    | exact superpose eq1132598 eq1132605
    | exact resolve eq1132605 eq1132598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132605
  have eq1132768 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq128405
       have i₂ := eq1132598 (τ (M.op (σ x) (σ y)))
       grind)
    | exact superpose eq1132598 eq128405
    | exact resolve eq128405 eq1132598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128405 eq1132598
  have eq1169764 : y = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1132627 (τ (M.op (σ x) (σ y)))
       have i₂ := eq1132768
       grind)
    | exact superpose eq1132768 eq1132627
    | exact resolve eq1132627 eq1132768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132627 eq1132768
  have eq1169969 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq508 x (M.op (σ x) (σ y))
       have i₂ := eq1169764
       grind)
    | exact superpose eq1169764 eq508
    | (have j0 := eq508 x (M.op (σ x) (σ y))
       grind)
    | exact resolve eq508 eq1169764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq1169764
  have eq1170018 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1169969
       have i₂ := eq124259
       grind)
    | exact superpose eq124259 eq1169969
    | exact resolve eq1169969 eq124259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124259 eq1169969
  have eq1170070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1170018
       have i₂ := eq43158
       grind)
    | exact superpose eq43158 eq1170018
    | exact resolve eq1170018 eq43158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43158 eq1170018
  have eq1170071 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1170070
  have eq1178086 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1170071
       grind)
    | exact superpose eq1170071 eq14
    | exact resolve eq14 eq1170071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170071
  have eq1178257 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1178086
       have i₂ := eq1132509
       grind)
    | exact superpose eq1132509 eq1178086
    | exact resolve eq1178086 eq1132509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132509 eq1178086
  have eq1178258 : False := by grind
  exact eq1178258

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4277 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X4 x X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X0 X1 X4 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X5 X6))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq20 X5 X6 x X4
       have i₂ := eq20 X1 X2 x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X1 (M.op X1 X2)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq150 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq164 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq150
    | exact resolve eq150 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq295 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq305 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq410 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq164 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq164
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq164 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k (M.op X2 (M.op X2 X3)) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    grind
  have eq584 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq35 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq35
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq647 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq647
    | (have j0 := eq647 (τ X0)
       grind)
    | exact resolve eq647 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1734 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1734
    | (have j0 := eq1734 X0
       grind)
    | exact resolve eq1734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1739 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1736 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736
    | (have j0 := eq1736 X0
       grind)
    | exact resolve eq1736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1766 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1862 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1884 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1739 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1739
    | (have j0 := eq1739 (τ X0)
       grind)
    | exact resolve eq1739 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1739
  have eq1886 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1927 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2418 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3112 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X0))
       have i₂ := eq142 X0 X0 X0
       grind)
    | exact superpose eq142 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq647 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3121 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3112 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1927 y x
       grind)
    | exact superpose eq1927 eq600
    | (have j1 := eq1927 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq1927 y x
       grind)
    | exact resolve eq600 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq3182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1862 y x
       grind)
    | exact superpose eq1862 eq600
    | (have j1 := eq1862 (σ y) (σ x)
       grind)
    | (have r₁ := eq600
       have r₂ := eq1862 y x
       grind)
    | exact resolve eq600 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1862
  have eq3183 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3182
  have eq3184 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq3181
  have eq3196 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq164
    | exact resolve eq164 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3196
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3196
    | exact resolve eq3196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3312 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3232
       grind)
    | exact superpose eq3232 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq3317 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq3312
  have eq4365 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq619
    | exact resolve eq619 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq4416 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4365
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4365
    | exact resolve eq4365 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4732 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq164 x
       have i₂ := eq3184
       grind)
    | exact superpose eq3184 eq164
    | exact resolve eq164 eq3184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3184
  have eq4778 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4732
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4732
    | exact resolve eq4732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4779 : x = (k x y) := by grind
  clear eq4778
  have eq4789 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X1 (τ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq4906 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4789 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq4789
    | (have j0 := eq4789 X0 X1
       grind)
    | exact resolve eq4789 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4789
  have eq4916 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4906 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4906
    | (have j0 := eq4906 X0 X1
       grind)
    | exact resolve eq4906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906
  have eq6835 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 x x x X0 X1 X2
       grind)
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq107 X0 X1 X2 x x x
       grind)
    | exact superpose eq107 eq305
    | exact resolve eq305 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq305
  have eq6855 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6835 X0 X1 X2
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq6835
    | (have j0 := eq6835 X0 X1 X2
       grind)
    | exact resolve eq6835 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779 eq6835
  have eq23352 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1884 (σ X0)
       have i₂ := eq410 (σ X0) X0
       grind)
    | exact superpose eq410 eq1884
    | (have j0 := eq1884 (σ X0)
       have j1 := eq410 (σ X0) X0
       grind)
    | exact resolve eq1884 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1884
  have eq23382 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23352 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23352
    | (have j0 := eq23352 X0
       grind)
    | exact resolve eq23352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23393 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23382 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23382
    | (have j0 := eq23382 X0
       grind)
    | exact resolve eq23382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23382
  have eq23397 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq23393 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23393
    | (have j0 := eq23393 X0
       grind)
    | exact resolve eq23393 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23393
  have eq23401 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23397 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq23397 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq23397 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq24512 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23401 x
       have i₂ := eq3183
       grind)
    | exact superpose eq3183 eq23401
    | (have j0 := eq23401 x
       grind)
    | exact resolve eq23401 eq3183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183 eq23401
  have eq24542 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24512
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24512
    | exact resolve eq24512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq28484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2418
       have i₂ := eq4916 x y
       grind)
    | exact superpose eq4916 eq2418
    | (have j1 := eq4916 x y
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4916 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2418 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq4916
  have eq28493 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq28484
  have eq33354 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X1))
       have i₂ := eq562 X0 X1 X0 X1
       grind)
    | exact superpose eq562 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq647 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq33403 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq33354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33354
  have eq34475 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4416
       grind)
    | exact superpose eq4416 eq9
    | exact resolve eq9 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq34584 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34475
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34475
    | exact resolve eq34475 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34475
  have eq35054 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq34584
       grind)
    | exact superpose eq34584 eq33
    | exact resolve eq33 eq34584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq34584
  have eq35073 : y = (M.op x x) ∨ x = y := by grind
  clear eq35054
  have eq35338 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq18
    | exact resolve eq18 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35341 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq35073
       grind)
    | exact superpose eq35073 eq57
    | exact resolve eq57 eq35073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq35073
  have eq35869 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 X0 (M.op X0 x)
       have i₂ := eq35338 X0 x
       grind)
    | exact superpose eq35338 eq35338
    | exact resolve eq35338 eq35338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36146 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq35869 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35869
  have eq36946 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  have eq40863 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq35338 X1 (M.op X1 x)
       have i₂ := eq35341 X1 x X0
       grind)
    | (have i₁ := eq35338 x (M.op x y)
       have i₂ := eq35341 X0 X1 x
       grind)
    | exact superpose eq35341 eq35338
    | exact resolve eq35338 eq35341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35341
  have eq41022 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq40863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40863
  have eq43165 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36946
       have i₂ := eq3317
       grind)
    | exact superpose eq3317 eq36946
    | exact resolve eq36946 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq36946
  have eq43185 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq43165
       have r₂ := eq24542
       grind)
    | exact resolve eq43165 eq24542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24542 eq43165
  have eq43273 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq43185
       grind)
    | exact superpose eq43185 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq43185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43185
  have eq43281 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq43273
  have eq43331 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85 x x
       have i₂ := eq43281
       grind)
    | exact superpose eq43281 eq85
    | (have j0 := eq85 x x
       grind)
    | (have r₁ := eq85 x x
       have r₂ := eq43281
       grind)
    | exact resolve eq85 eq43281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43371 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq43281
  have eq43373 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq85 x x
       grind)
    | (have r₁ := eq43331
       have r₂ := eq85 x x
       grind)
    | exact resolve eq43331 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq43331
  have eq47264 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X2 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq18
    | exact resolve eq18 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq47281 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35338 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq35338
    | exact resolve eq35338 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47288 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq47281 X0
       have i₂ := eq3121 X0
       grind)
    | exact superpose eq3121 eq47281
    | exact resolve eq47281 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121 eq47281
  have eq47305 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47264 X0 X1 X2
       have i₂ := eq33403 X0 X0
       grind)
    | exact superpose eq33403 eq47264
    | exact resolve eq47264 eq33403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33403 eq47264
  have eq47598 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq47305 (M.op x y) X0 X1
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47305
    | exact resolve eq47305 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47305
  have eq53635 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq47288 (M.op x y)
       have i₂ := eq41022 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq41022 eq47288
    | exact resolve eq47288 eq41022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41022 eq47288
  have eq53667 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq53635
  have eq54011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6855 x x x
       have i₂ := eq47598 x (M.op x x)
       grind)
    | exact superpose eq47598 eq6855
    | (have r₁ := eq6855 x x x
       have r₂ := eq47598 x (M.op x x)
       grind)
    | exact resolve eq6855 eq47598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855 eq47598
  have eq54101 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq54011
  have eq54151 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq14
    | exact resolve eq14 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54202 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35338 (σ x) (σ y)
       have i₂ := eq54101
       grind)
    | exact superpose eq54101 eq35338
    | exact resolve eq35338 eq54101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35338
  have eq54229 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq54202
  have eq54263 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq53667
       grind)
    | exact superpose eq53667 eq54151
    | exact resolve eq54151 eq53667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53667
  have eq54264 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq54151
       have i₂ := eq28493
       grind)
    | exact superpose eq28493 eq54151
    | (have r₁ := eq54151
       have r₂ := eq28493
       grind)
    | exact resolve eq54151 eq28493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28493 eq54151
  have eq54268 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) := by grind
  clear eq54264
  have eq54269 : y = (k x x) ∨ x = y := by grind
  clear eq54268
  have eq54270 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq54263
  have eq56002 : (M.op x y) = (σ (k x x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35 x x
       have i₂ := eq54229
       grind)
    | exact superpose eq54229 eq35
    | exact resolve eq35 eq54229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq54229
  have eq56102 : (M.op x y) = (σ (k x x)) ∨ x = y := by
    first
    | (have r₁ := eq56002
       have r₂ := eq54270
       grind)
    | exact resolve eq56002 eq54270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56002
  have eq56149 : (M.op x y) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq56102
       have i₂ := eq54269
       grind)
    | exact superpose eq54269 eq56102
    | exact resolve eq56102 eq54269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54269 eq56102
  have eq56181 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq56149
  have eq56198 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36146 X0
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq36146
    | exact resolve eq36146 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36146
  have eq56206 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54270
       have i₂ := eq56181
       grind)
    | exact superpose eq56181 eq54270
    | exact resolve eq54270 eq56181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54270 eq56181
  have eq56264 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq56206
  have eq56272 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq56198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56198
  have eq57259 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq54101
       have i₂ := eq56272 (σ x)
       grind)
    | exact superpose eq56272 eq54101
    | exact resolve eq54101 eq56272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54101 eq56272
  have eq57266 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq57259
  have eq57279 : x = y := by
    first
    | (have r₁ := eq57266
       have r₂ := eq56264
       grind)
    | exact resolve eq57266 eq56264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56264 eq57266
  have eq57296 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq14
    | exact resolve eq14 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57310 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43371
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43371
    | (have r₁ := eq43371
       have r₂ := eq57279
       grind)
    | exact resolve eq43371 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43371
  have eq57311 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq43373
       have i₂ := eq57279
       grind)
    | exact superpose eq57279 eq43373
    | (have r₁ := eq43373
       have r₂ := eq57279
       grind)
    | exact resolve eq43373 eq57279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43373 eq57279
  have eq57314 : x = (k x x) := by grind
  clear eq57311
  have eq57315 : x = (M.op x x) := by grind
  clear eq57310
  have eq57322 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57296
       have i₂ := eq57315
       grind)
    | exact superpose eq57315 eq57296
    | exact resolve eq57296 eq57315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296 eq57315
  have eq57347 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq57314
       grind)
    | exact superpose eq57314 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq57314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq57314
  have eq57388 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq57347
  have eq57406 : False := by grind
  exact eq57406

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4277 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4277 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X3 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X2 X3)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X4 x X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 X4 (M.op X4 x)
       have i₂ := eq18 X0 X1 X4 x
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq80 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq106 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X4 (M.op X5 (M.op X5 X6))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq20 X5 X6 x X4
       have i₂ := eq20 X1 X2 x X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  clear eq20
  have eq280 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq30 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq305 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X1)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    grind
  have eq584 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1766 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1862 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1886 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1927 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2418 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq14
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq14 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3113 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X0))
       have i₂ := eq141 X0 X0 X0
       grind)
    | exact superpose eq141 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq647 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3122 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113
  have eq3183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1927 y x
       grind)
    | exact superpose eq1927 eq600
    | (have j1 := eq1927 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq1927 y x
       grind)
    | exact resolve eq600 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq3184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq1862 y x
       grind)
    | exact superpose eq1862 eq600
    | (have j1 := eq1862 (σ y) (σ x)
       grind)
    | (have r₁ := eq600
       have r₂ := eq1862 y x
       grind)
    | exact resolve eq600 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1862
  have eq3185 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3184
  have eq3186 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq3183
  have eq4368 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq3185
       grind)
    | exact superpose eq3185 eq619
    | exact resolve eq619 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq4419 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4368
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4368
    | exact resolve eq4368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq4735 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq3186
       grind)
    | exact superpose eq3186 eq80
    | exact resolve eq80 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq4781 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4735
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4735
    | exact resolve eq4735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq4782 : x = (k y x) := by grind
  clear eq4781
  have eq4792 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X1 (τ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq4909 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4792 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq4792
    | (have j0 := eq4792 X0 X1
       grind)
    | exact resolve eq4792 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4792
  have eq4919 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4909 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4909
    | (have j0 := eq4909 X0 X1
       grind)
    | exact resolve eq4909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909
  have eq6838 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq106 x x x X0 X1 X2
       grind)
    | (have i₁ := eq305 x (M.op x x)
       have i₂ := eq106 X0 X1 X2 x x x
       grind)
    | exact superpose eq106 eq305
    | exact resolve eq305 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq305
  have eq6858 : ∀ X0 X1 X2 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 (M.op X1 X2))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6838 X0 X1 X2
       have i₂ := eq4782
       grind)
    | exact superpose eq4782 eq6838
    | (have j0 := eq6838 X0 X1 X2
       grind)
    | exact resolve eq6838 eq4782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782 eq6838
  have eq25638 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq4419
       grind)
    | exact superpose eq4419 eq9
    | exact resolve eq9 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq25740 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25638
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq25638
    | exact resolve eq25638 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25638
  have eq25987 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq25740
       grind)
    | exact superpose eq25740 eq31
    | exact resolve eq31 eq25740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq25740
  have eq26001 : y = (M.op x x) ∨ x = y := by grind
  clear eq25987
  have eq26356 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq80
    | (have j1 := eq95 (σ X1) X0
       grind)
    | exact resolve eq80 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq95
  have eq26601 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26356 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq26356
    | (have j0 := eq26356 X0 X1
       grind)
    | exact resolve eq26356 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq26692 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26601 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq26601
    | (have j0 := eq26601 X0 X1
       grind)
    | exact resolve eq26601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26601
  have eq26720 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq26001
       grind)
    | exact superpose eq26001 eq18
    | exact resolve eq18 eq26001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26723 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op x y)) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq26001
       grind)
    | exact superpose eq26001 eq57
    | exact resolve eq57 eq26001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq26001
  have eq26900 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26720 X0 (M.op X0 x)
       have i₂ := eq26720 X0 x
       grind)
    | exact superpose eq26720 eq26720
    | exact resolve eq26720 eq26720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27135 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq26900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900
  have eq28344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2418
       have i₂ := eq4919 x y
       grind)
    | exact superpose eq4919 eq2418
    | (have j1 := eq4919 x y
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4919 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2418
       have r₂ := eq4919 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2418 eq4919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq4919
  have eq28353 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq28344
  have eq32422 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) ≠ (σ (M.op X0 (M.op X0 X1))) ∨ (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 (M.op X0 (M.op X0 X1))
       have i₂ := eq562 X0 X1 X0 X1
       grind)
    | exact superpose eq562 eq647
    | (have j0 := eq647 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq647 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq32469 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 (M.op X0 X1))) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq32422 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32422
  have eq33236 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq26720 X1 (M.op X1 x)
       have i₂ := eq26723 X1 x X0
       grind)
    | (have i₁ := eq26720 x (M.op x y)
       have i₂ := eq26723 X0 X1 x
       grind)
    | exact superpose eq26723 eq26720
    | exact resolve eq26720 eq26723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26723
  have eq33370 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op X0 (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq33236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33236
  have eq36194 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26692 x x
       have i₂ := eq3185
       grind)
    | exact superpose eq3185 eq26692
    | (have j0 := eq26692 x x
       grind)
    | exact resolve eq26692 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185 eq26692
  have eq36280 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36194
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq36194
    | exact resolve eq36194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36194
  have eq51692 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36280
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq36280
    | (have j1 := eq12 y x
       grind)
    | exact resolve eq36280 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36280
  have eq51752 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq51692
  have eq52327 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq87 x x
       have i₂ := eq51752
       grind)
    | exact superpose eq51752 eq87
    | (have j0 := eq87 x x
       grind)
    | (have r₁ := eq87 x x
       have r₂ := eq51752
       grind)
    | exact resolve eq87 eq51752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52372 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq51752
  have eq52374 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq87 x x
       grind)
    | (have r₁ := eq52327
       have r₂ := eq87 x x
       grind)
    | exact resolve eq52327 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq52327
  have eq66149 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X2 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq18
    | exact resolve eq18 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66225 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26720 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq26720
    | exact resolve eq26720 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66246 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq66225 X0
       have i₂ := eq3122 X0
       grind)
    | exact superpose eq3122 eq66225
    | exact resolve eq66225 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122 eq66225
  have eq66322 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66149 X0 X1 X2
       have i₂ := eq32469 X0 X0
       grind)
    | exact superpose eq32469 eq66149
    | exact resolve eq66149 eq32469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32469 eq66149
  have eq66765 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq66322 (M.op x y) X0 X1
       have i₂ := eq33370 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq33370 eq66322
    | exact resolve eq66322 eq33370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66322
  have eq94045 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq66246 (M.op x y)
       have i₂ := eq33370 (M.op x y) (M.op x y)
       grind)
    | exact superpose eq33370 eq66246
    | exact resolve eq66246 eq33370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33370 eq66246
  have eq94259 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq94045
  have eq99110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6858 x x x
       have i₂ := eq66765 x (M.op x x)
       grind)
    | exact superpose eq66765 eq6858
    | (have r₁ := eq6858 x x x
       have r₂ := eq66765 x (M.op x x)
       grind)
    | exact resolve eq6858 eq66765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858 eq66765
  have eq99293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq99110
  have eq100846 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq99293
       grind)
    | exact superpose eq99293 eq14
    | exact resolve eq14 eq99293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100964 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq26720 (σ x) (σ y)
       have i₂ := eq99293
       grind)
    | exact superpose eq99293 eq26720
    | exact resolve eq26720 eq99293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26720
  have eq100992 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq100964
  have eq102381 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq100846
       have i₂ := eq94259
       grind)
    | exact superpose eq94259 eq100846
    | exact resolve eq100846 eq94259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94259
  have eq102382 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq100846
       have i₂ := eq28353
       grind)
    | exact superpose eq28353 eq100846
    | (have r₁ := eq100846
       have r₂ := eq28353
       grind)
    | exact resolve eq100846 eq28353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28353 eq100846
  have eq102391 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (k x x) := by grind
  clear eq102382
  have eq102392 : y = (k x x) ∨ x = y := by grind
  clear eq102391
  have eq102393 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq102381
  have eq108058 : (M.op x y) = (σ (k x x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq100992
       grind)
    | exact superpose eq100992 eq33
    | exact resolve eq33 eq100992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq100992
  have eq108263 : (M.op x y) = (σ (k x x)) ∨ x = y := by
    first
    | (have r₁ := eq108058
       have r₂ := eq102393
       grind)
    | exact resolve eq108058 eq102393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108058
  have eq111107 : (M.op x y) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq108263
       have i₂ := eq102392
       grind)
    | exact superpose eq102392 eq108263
    | exact resolve eq108263 eq102392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102392 eq108263
  have eq111285 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq111107
  have eq112062 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq27135 X0
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq27135
    | exact resolve eq27135 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27135
  have eq112073 : (σ x) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq102393
       have i₂ := eq111285
       grind)
    | exact superpose eq111285 eq102393
    | exact resolve eq102393 eq111285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102393 eq111285
  have eq112167 : (σ x) ≠ (σ y) ∨ x = y := by grind
  clear eq112073
  have eq112176 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq112062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112062
  have eq126072 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq99293
       have i₂ := eq112176 (σ x)
       grind)
    | exact superpose eq112176 eq99293
    | exact resolve eq99293 eq112176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99293 eq112176
  have eq126085 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq126072
  have eq126101 : x = y := by
    first
    | (have r₁ := eq126085
       have r₂ := eq112167
       grind)
    | exact resolve eq126085 eq112167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112167 eq126085
  have eq126748 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq14
    | exact resolve eq14 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126761 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52372
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq52372
    | (have r₁ := eq52372
       have r₂ := eq126101
       grind)
    | exact resolve eq52372 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52372
  have eq126762 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq52374
       have i₂ := eq126101
       grind)
    | exact superpose eq126101 eq52374
    | (have r₁ := eq52374
       have r₂ := eq126101
       grind)
    | exact resolve eq52374 eq126101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52374 eq126101
  have eq126765 : x = (k x x) := by grind
  clear eq126762
  have eq126766 : x = (M.op x x) := by grind
  clear eq126761
  have eq126772 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq126748
       have i₂ := eq126766
       grind)
    | exact superpose eq126766 eq126748
    | exact resolve eq126748 eq126766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126748 eq126766
  have eq127922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq126765
       grind)
    | exact superpose eq126765 eq647
    | (have j0 := eq647 x
       grind)
    | exact resolve eq647 eq126765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq126765
  have eq127965 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq127922
  have eq127984 : False := by grind
  exact eq127984

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4279 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X3
       have i₂ := eq8 X0 X3 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq29 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X5 X4 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X0 X1 X5 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op X3 X4) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X4 X3 X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X3 X4) X4
       have i₂ := eq18 X0 X1 X4 X3
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq33
    | exact resolve eq33 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq33 (τ X1) X0
       grind)
    | exact superpose eq33 eq17
    | (have j1 := eq33 (τ X1) X0
       grind)
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq29 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq160 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq21
  have eq286 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq32 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq312 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq419 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq160 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq160
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq9
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1370 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq584 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq584
    | (have j0 := eq584 (τ X0)
       grind)
    | exact resolve eq584 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1370
    | (have j0 := eq1370 X0
       grind)
    | exact resolve eq1370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1375 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1372 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1372
    | (have j0 := eq1372 X0
       grind)
    | exact resolve eq1372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1398 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X0 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1511 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1375 (τ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq1375
    | (have j0 := eq1375 (τ X0)
       grind)
    | exact resolve eq1375 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1375
  have eq1513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1554 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq2039 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq18
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq18 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1554 y x
       grind)
    | exact superpose eq1554 eq535
    | (have j1 := eq1554 y x
       grind)
    | (have r₁ := eq535
       have r₂ := eq1554 y x
       grind)
    | exact resolve eq535 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1489 y x
       grind)
    | exact superpose eq1489 eq535
    | (have j1 := eq1489 (σ y) (σ x)
       grind)
    | (have r₁ := eq535
       have r₂ := eq1489 y x
       grind)
    | exact resolve eq535 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2410 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2409
  have eq2411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2408
  have eq2423 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq160
    | exact resolve eq160 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2423
    | exact resolve eq2423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2536 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2539 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1489 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq1489
    | (have j0 := eq1489 y x
       grind)
    | exact resolve eq1489 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2456
  have eq2540 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2539
  have eq2541 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2536
  have eq2591 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq554
    | exact resolve eq554 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2633 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2591
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2591
    | exact resolve eq2591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2646 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y x
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq18
    | exact resolve eq18 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3776 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq160 x
       have i₂ := eq2411
       grind)
    | exact superpose eq2411 eq160
    | exact resolve eq160 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq2411
  have eq3824 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3776
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3776
    | exact resolve eq3776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3825 : x = (k x y) := by grind
  clear eq3824
  have eq5341 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq2646
    | exact resolve eq2646 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5461 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5341
  have eq5885 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq14
    | exact resolve eq14 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq6348 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5885
       have i₂ := eq2540
       grind)
    | exact superpose eq2540 eq5885
    | exact resolve eq5885 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540 eq5885
  have eq6349 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq6348
  have eq8009 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq8086 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8009 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq8009
    | (have j0 := eq8009 X0 X1
       grind)
    | exact resolve eq8009 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq21291 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1511 (σ X0)
       have i₂ := eq419 (σ X0) X0
       grind)
    | exact superpose eq419 eq1511
    | (have j0 := eq1511 (σ X0)
       have j1 := eq419 (σ X0) X0
       grind)
    | exact resolve eq1511 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq21315 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21291 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21291
    | (have j0 := eq21291 X0
       grind)
    | exact resolve eq21291 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21323 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21315 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21315
    | (have j0 := eq21315 X0
       grind)
    | exact resolve eq21315 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21315
  have eq21325 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq21323 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21323
    | (have j0 := eq21323 X0
       grind)
    | exact resolve eq21323 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21323
  have eq21327 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21325 X0
       have j1 := eq85 X0 X0
       grind)
    | (have r₁ := eq21325 x
       have r₂ := eq85 x x
       grind)
    | exact resolve eq21325 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq21325
  have eq22214 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21327 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq21327
    | (have j0 := eq21327 x
       grind)
    | exact resolve eq21327 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21327
  have eq22240 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22214
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22214
    | exact resolve eq22214 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22214
  have eq25535 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2633
       grind)
    | exact superpose eq2633 eq9
    | exact resolve eq9 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633
  have eq25604 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25535
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq25535
    | exact resolve eq25535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25535
  have eq26593 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33 x x
       have i₂ := eq25604
       grind)
    | exact superpose eq25604 eq33
    | exact resolve eq33 eq25604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq25604
  have eq26606 : y = (M.op x x) ∨ x = y := by grind
  clear eq26593
  have eq27635 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq26606
       grind)
    | exact superpose eq26606 eq18
    | exact resolve eq18 eq26606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26606
  have eq28743 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq27635 (M.op X0 X1) X1
       have i₂ := eq27635 X1 X0
       grind)
    | exact superpose eq27635 eq27635
    | exact resolve eq27635 eq27635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27635
  have eq29070 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq28743 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28743
  have eq32461 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq29070
  have eq33274 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32461
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq32461
    | exact resolve eq32461 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq32461
  have eq33332 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33274
       have r₂ := eq22240
       grind)
    | exact resolve eq33274 eq22240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240 eq33274
  have eq34362 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq33332
       grind)
    | exact superpose eq33332 eq584
    | (have j0 := eq584 x
       grind)
    | exact resolve eq584 eq33332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq33332
  have eq34386 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq34362
  have eq41020 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2410
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2410
    | exact resolve eq2410 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq41169 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2646 (σ x) (σ x)
       have i₂ := eq34386
       grind)
    | exact superpose eq34386 eq2646
    | exact resolve eq2646 eq34386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq41173 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq41169
  have eq41178 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq41020
  have eq50975 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq34386
       have i₂ := eq41173
       grind)
    | exact superpose eq41173 eq34386
    | exact resolve eq34386 eq41173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34386 eq41173
  have eq51084 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq50975
  have eq51093 : y = (M.op x x) := by
    first
    | (have r₁ := eq51084
       have r₂ := eq6349
       grind)
    | exact resolve eq51084 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349 eq51084
  have eq52251 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq212 X0 x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq212
    | exact resolve eq212 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq52278 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq18
    | exact resolve eq18 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52282 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X0 X1 X2 X3
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq57
    | exact resolve eq57 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq52286 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X1 X2 X0 x x
       have i₂ := eq51093
       grind)
    | exact superpose eq51093 eq69
    | exact resolve eq69 eq51093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq51093
  have eq52362 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq52251 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq52251
    | exact resolve eq52251 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52251
  have eq53771 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52278 (M.op X0 X1) X1
       have i₂ := eq52278 X1 X0
       grind)
    | exact superpose eq52278 eq52278
    | exact resolve eq52278 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57047 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    first
    | (have i₁ := eq1511 (M.op x y)
       have i₂ := eq52362
       grind)
    | exact superpose eq52362 eq1511
    | (have j0 := eq1511 (M.op x y)
       grind)
    | exact resolve eq1511 eq52362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq52362
  have eq57061 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by grind
  clear eq57047
  have eq63093 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1461 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq63094 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63093 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63093
    | (have j0 := eq63093 X0
       grind)
    | exact resolve eq63093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63093
  have eq63140 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq63094 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq63094
    | (have j0 := eq63094 (σ X0)
       grind)
    | exact resolve eq63094 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63094
  have eq63150 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63140 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63140
    | (have j0 := eq63140 X0
       grind)
    | exact resolve eq63140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63140
  have eq71931 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63150 X0
       have i₂ := eq8086 X0 X0
       grind)
    | exact superpose eq8086 eq63150
    | (have j0 := eq63150 X0
       have j1 := eq8086 X0 X0
       grind)
    | (have r₁ := eq63150 x
       have r₂ := eq8086 x x
       grind)
    | exact resolve eq63150 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086 eq63150
  have eq71938 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71931
  have eq71968 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71938 x
       have i₂ := eq41178
       grind)
    | exact superpose eq41178 eq71938
    | exact resolve eq71938 eq41178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41178 eq71938
  have eq72004 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq71968
  have eq74048 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq52282 (τ (M.op x y)) (τ (M.op x y)) X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52282
    | exact resolve eq52282 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52282
  have eq74054 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (τ (M.op x y)) (τ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq52286 X0 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq52286
    | exact resolve eq52286 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52286
  have eq74056 : (M.op x y) = (M.op (τ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq53771 (τ (M.op x y)) (τ (M.op x y))
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq53771
    | exact resolve eq53771 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74059 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq74054 X0
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74054
    | exact resolve eq74054 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74054
  have eq74065 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (τ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq74048 X0 X1
       have i₂ := eq57061
       grind)
    | exact superpose eq57061 eq74048
    | exact resolve eq74048 eq57061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57061 eq74048
  have eq74173 : (M.op x y) = (M.op y (τ (M.op x y))) := by
    first
    | (have i₁ := eq74059 x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq74059
    | exact resolve eq74059 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74059
  have eq74177 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq74065 x x
       have i₂ := eq53771 x x
       grind)
    | exact superpose eq53771 eq74065
    | exact resolve eq74065 eq53771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53771 eq74065
  have eq74351 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq74177
       grind)
    | exact superpose eq74177 eq10
    | exact resolve eq10 eq74177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74177
  have eq74568 : (σ (M.op x y)) ≠ (M.op (τ (M.op x y)) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq312 (τ (M.op x y)) y
       have i₂ := eq74173
       grind)
    | exact superpose eq74173 eq312
    | exact resolve eq312 eq74173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq74173
  have eq74622 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq74568
       have i₂ := eq74056
       grind)
    | exact superpose eq74056 eq74568
    | exact resolve eq74568 eq74056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74056 eq74568
  have eq74668 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq74622
       have r₂ := eq74351
       grind)
    | exact resolve eq74622 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74622
  have eq74681 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74668
       have i₂ := eq3825
       grind)
    | exact superpose eq3825 eq74668
    | exact resolve eq74668 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq74668
  have eq74727 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq14
    | exact resolve eq14 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74843 : (M.op x y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq52278 (σ y) (σ x)
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq52278
    | exact resolve eq52278 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74960 : (M.op x y) ≠ (σ x) := by
    first
    | (have i₁ := eq74727
       have i₂ := eq74351
       grind)
    | exact superpose eq74351 eq74727
    | exact resolve eq74727 eq74351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74351 eq74727
  have eq76765 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2039 x x x x
       have i₂ := eq72004
       grind)
    | exact superpose eq72004 eq2039
    | exact resolve eq2039 eq72004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039 eq72004
  have eq76809 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq76765 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76765
  have eq76821 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76809 x x
       have i₂ := eq52278 x x
       grind)
    | exact superpose eq52278 eq76809
    | exact resolve eq76809 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52278 eq76809
  have eq76839 : (M.op x y) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76821
       have i₂ := eq74681
       grind)
    | exact superpose eq74681 eq76821
    | exact resolve eq76821 eq74681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76821
  have eq76841 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq76839
       have r₂ := eq74960
       grind)
    | exact resolve eq76839 eq74960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76839
  have eq76843 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74843
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74843
    | exact resolve eq74843 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74843
  have eq76844 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74681
       have i₂ := eq76841
       grind)
    | exact superpose eq76841 eq74681
    | exact resolve eq74681 eq76841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74681 eq76841
  have eq76946 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq76843
       have i₂ := eq76844
       grind)
    | exact superpose eq76844 eq76843
    | exact resolve eq76843 eq76844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76843 eq76844
  have eq76948 : False := by grind
  exact eq76948

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pyx_Equation4279 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8 x X3 X4
       have i₂ := eq8 x X0 X1
       grind)
    | (have i₁ := eq8 x X1 x
       have i₂ := eq8 X0 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X3) X3
       have i₂ := eq8 X0 X3 X2
       grind)
    | (have i₁ := eq8 X0 (M.op X0 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op X3 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq45 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X4 X5) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X5 X4 X0 X1
       grind)
    | (have i₁ := eq18 X2 X3 (M.op X4 X5) X5
       have i₂ := eq18 X0 X1 X5 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq27
  have eq80 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq31 (τ X1) X0
       grind)
    | exact superpose eq31 eq16
    | (have j1 := eq31 (τ X1) X0
       grind)
    | exact resolve eq16 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq95 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq42
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq144 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1
       have i₂ := eq12 X0 (τ X1)
       grind)
    | (have i₁ := eq45 X0
       have i₂ := eq12 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq12 eq45
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq212 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (k (M.op X0 (M.op X0 X0)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq21
  have eq286 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq30 (σ y) (σ x) X0 X1
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 (σ y) (σ x) x x
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq312 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1029 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    grind
  clear eq57
  have eq1398 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1513 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1513 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1513
    | (have j0 := eq1513 X0 X1
       grind)
    | exact resolve eq1513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq2038 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X3 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq18
    | (have j1 := eq81 X0 X1
       grind)
    | exact resolve eq18 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2338 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq584 (M.op X0 (M.op X0 X0))
       have i₂ := eq212 X0 X0
       grind)
    | exact superpose eq212 eq584
    | (have j0 := eq584 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq584 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2345 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq2338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1554 y x
       grind)
    | exact superpose eq1554 eq535
    | (have j1 := eq1554 y x
       grind)
    | (have r₁ := eq535
       have r₂ := eq1554 y x
       grind)
    | exact resolve eq535 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq2409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq535
       have i₂ := eq1489 y x
       grind)
    | exact superpose eq1489 eq535
    | (have j1 := eq1489 (σ y) (σ x)
       grind)
    | (have r₁ := eq535
       have r₂ := eq1489 y x
       grind)
    | exact resolve eq535 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2410 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2409
  have eq2411 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k y x) := by grind
  clear eq2408
  have eq2423 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq80
    | exact resolve eq80 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2456 : x = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2423
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2423
    | exact resolve eq2423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2537 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2540 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1489 y x
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq1489
    | (have j0 := eq1489 y x
       grind)
    | exact resolve eq1489 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq2456
  have eq2541 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2540
  have eq2542 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq2537
  have eq2592 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq554 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq554
    | exact resolve eq554 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2634 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2592
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2592
    | exact resolve eq2592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2647 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 y x
       have i₂ := eq2542
       grind)
    | exact superpose eq2542 eq18
    | exact resolve eq18 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq3777 : x = (k (τ (σ y)) x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq2411
       grind)
    | exact superpose eq2411 eq80
    | exact resolve eq80 eq2411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq3825 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3777
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3777
    | exact resolve eq3777 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3826 : x = (k y x) := by grind
  clear eq3825
  have eq5343 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2647 (σ x) (σ x)
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq2647
    | exact resolve eq2647 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5463 : (M.op (σ x) (σ y)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq5343
  have eq5887 : (σ (M.op x y)) ≠ (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5463
       grind)
    | exact superpose eq5463 eq14
    | exact resolve eq14 eq5463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq6350 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5887
       have i₂ := eq2541
       grind)
    | exact superpose eq2541 eq5887
    | exact resolve eq5887 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq5887
  have eq6351 : (σ x) ≠ (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq6350
  have eq9349 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq144 X1 (σ X0)
       grind)
    | exact superpose eq144 eq13
    | (have j1 := eq144 X1 (σ X0)
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9404 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9349 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9349
    | (have j0 := eq9349 X0 X1
       grind)
    | exact resolve eq9349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq22942 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2634
       grind)
    | exact superpose eq2634 eq9
    | exact resolve eq9 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq23003 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22942
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq22942
    | exact resolve eq22942 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22942
  have eq23528 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq23003
       grind)
    | exact superpose eq23003 eq31
    | exact resolve eq31 eq23003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq23003
  have eq23541 : y = (M.op x x) ∨ x = y := by grind
  clear eq23528
  have eq48022 : (τ (σ y)) = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95 (σ x) x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq95
    | exact resolve eq95 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48412 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq80
    | (have j1 := eq95 (σ X1) X0
       grind)
    | exact resolve eq80 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq95
  have eq48626 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48412 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48412
    | (have j0 := eq48412 X0 X1
       grind)
    | exact resolve eq48412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48412
  have eq48676 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48022
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq48022
    | exact resolve eq48022 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48022
  have eq48714 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48626 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq48626
    | (have j0 := eq48626 X0 X1
       grind)
    | exact resolve eq48626 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48626
  have eq48721 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48676
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq48676
    | exact resolve eq48676 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48676
  have eq52920 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq48714 x x
       have i₂ := eq2410
       grind)
    | exact superpose eq2410 eq48714
    | (have j0 := eq48714 x x
       grind)
    | exact resolve eq48714 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq48714
  have eq53001 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52920
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq52920
    | exact resolve eq52920 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52920
  have eq53855 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9404 x x
       have i₂ := eq48721
       grind)
    | exact superpose eq48721 eq9404
    | exact resolve eq9404 eq48721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9404 eq48721
  have eq53860 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq53855
  have eq60736 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq53001
  have eq60758 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq60736
       have r₂ := eq23541
       grind)
    | exact resolve eq60736 eq23541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23541 eq60736
  have eq66150 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq60758
       grind)
    | exact superpose eq60758 eq584
    | (have j0 := eq584 x
       grind)
    | exact resolve eq584 eq60758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60758
  have eq66178 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq66150
  have eq68373 : ∀ X0 : G, (k X0 (σ (τ X0))) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1461 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq68374 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68373 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68373
    | (have j0 := eq68373 X0
       grind)
    | exact resolve eq68373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68373
  have eq68607 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq68374 (σ X0)
       have i₂ := eq144 X0 (σ X0)
       grind)
    | exact superpose eq144 eq68374
    | (have j0 := eq68374 (σ X0)
       have j1 := eq144 X0 (σ X0)
       grind)
    | (have r₁ := eq68374 (σ X0)
       have r₂ := eq144 X0 (σ X0)
       grind)
    | exact resolve eq68374 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq68374
  have eq68617 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq68607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68607
  have eq68622 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq68617 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68617
    | (have j0 := eq68617 X0
       grind)
    | exact resolve eq68617 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68617
  have eq68630 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq68622 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq68622
    | (have j0 := eq68622 X0
       grind)
    | exact resolve eq68622 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68622
  have eq71018 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) ≠ (σ (M.op X0 (M.op X1 X0))) ∨ (σ (M.op X0 (M.op X1 X0))) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq584 (M.op X0 (M.op X1 X0))
       have i₂ := eq1029 X0 X1 X0 X1
       grind)
    | exact superpose eq1029 eq584
    | (have j0 := eq584 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq584 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq1029
  have eq71074 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (σ (M.op X0 (M.op X1 X0))) (σ (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq71018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71018
  have eq71292 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2647 (σ x) (σ x)
       have i₂ := eq66178
       grind)
    | exact superpose eq66178 eq2647
    | exact resolve eq2647 eq66178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq71297 : (M.op (σ x) (σ x)) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq71292
  have eq74258 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68630 x
       have i₂ := eq53860
       grind)
    | exact superpose eq53860 eq68630
    | exact resolve eq68630 eq53860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53860 eq68630
  have eq74456 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq74258
  have eq88753 : (σ x) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66178
       have i₂ := eq71297
       grind)
    | exact superpose eq71297 eq66178
    | exact resolve eq66178 eq71297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66178 eq71297
  have eq88976 : (σ x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq88753
  have eq88990 : y = (M.op x x) := by
    first
    | (have r₁ := eq88976
       have r₂ := eq6351
       grind)
    | exact resolve eq88976 eq6351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6351 eq88976
  have eq90456 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x x
       have i₂ := eq88990
       grind)
    | exact superpose eq88990 eq18
    | exact resolve eq18 eq88990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq88990
  have eq126083 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq2038 x x x x
       have i₂ := eq74456
       grind)
    | exact superpose eq74456 eq2038
    | exact resolve eq2038 eq74456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038 eq74456
  have eq126711 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X1 X0)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq126083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126083
  have eq126919 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126711 x x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq126711
    | exact resolve eq126711 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126711
  have eq129172 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq312 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq312
    | exact resolve eq312 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq129217 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq90456 (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq90456
    | exact resolve eq90456 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129248 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq129217 X0
       have i₂ := eq71074 X0 X0
       grind)
    | exact superpose eq71074 eq129217
    | exact resolve eq129217 eq71074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71074 eq129217
  have eq129292 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq129172 X0
       have i₂ := eq2345 X0
       grind)
    | exact superpose eq2345 eq129172
    | exact resolve eq129172 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345 eq129172
  have eq129667 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq129248 x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq129248
    | exact resolve eq129248 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129248
  have eq129710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq129292 x
       have i₂ := eq90456 x x
       grind)
    | exact superpose eq90456 eq129292
    | exact resolve eq129292 eq90456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129292
  have eq129711 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq129710
  have eq130062 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129711
       have i₂ := eq3826
       grind)
    | exact superpose eq3826 eq129711
    | exact resolve eq129711 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826 eq129711
  have eq130611 : (M.op x y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq90456 (σ y) (σ x)
       have i₂ := eq130062
       grind)
    | exact superpose eq130062 eq90456
    | exact resolve eq90456 eq130062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90456 eq130062
  have eq181201 : (M.op x y) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126919
       grind)
    | exact superpose eq126919 eq14
    | exact resolve eq14 eq126919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126919
  have eq181333 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq181201
       have r₂ := eq129667
       grind)
    | exact resolve eq181201 eq129667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181201
  have eq181369 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq181333
       grind)
    | exact superpose eq181333 eq14
    | exact resolve eq14 eq181333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181374 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq130611
       have i₂ := eq181333
       grind)
    | exact superpose eq181333 eq130611
    | exact resolve eq130611 eq181333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130611 eq181333
  have eq181549 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq181369
       have i₂ := eq181374
       grind)
    | exact superpose eq181374 eq181369
    | exact resolve eq181369 eq181374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181369 eq181374
  have eq181567 : False := by grind
  exact eq181567

/-- `Equation4286`: `x ◇ (x ◇ y) = x ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4286 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4286 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4286.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X0 x X3
       have i₂ := eq8 X0 x X1
       grind)
    | (have i₁ := eq8 x x x
       have i₂ := eq8 x X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X0 X2 x
       grind)
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq8 X1 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145 X0 (M.op X0 X2)
       have i₂ := eq25 X0 X2 X1
       grind)
    | (have i₁ := eq145 X0 (M.op X0 X2)
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq145
    | (have j0 := eq145 X0 (M.op X0 X2)
       grind)
    | (have r₁ := eq145 X0 (M.op X0 (M.op X0 X2))
       have r₂ := eq25 X0 (M.op X0 X2) X2
       grind)
    | (have r₁ := eq145 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq25 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq145 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq409 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq36 x y
       grind)
    | exact superpose eq36 eq14
    | (have j1 := eq36 x y
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 (σ X0))) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq8
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq8 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq9
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq13
    | (have j1 := eq36 X0 X2
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq871 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq934 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq871 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq871
    | (have j0 := eq871 X0 X1
       grind)
    | exact resolve eq871 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1533 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq409
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq409
    | (have j1 := eq934 (σ y) (σ x)
       grind)
    | (have r₁ := eq409
       have r₂ := eq934 y x
       grind)
    | exact resolve eq409 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1534 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1533
  have eq11711 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq412 (τ X0) (τ X1) X2
       have i₂ := eq73 X1 X0
       grind)
    | exact superpose eq73 eq412
    | (have j0 := eq412 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq412 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq11902 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11711 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11711
    | (have j0 := eq11711 X0 X1 X2
       grind)
    | exact resolve eq11711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711
  have eq11907 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11902 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11902
    | (have j0 := eq11902 X0 X1 X2
       grind)
    | exact resolve eq11902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq11908 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11907 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11907
    | (have j0 := eq11907 X0 X1 X2
       grind)
    | exact resolve eq11907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq11909 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11908 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11908
    | (have j0 := eq11908 X0 X1 X2
       grind)
    | exact resolve eq11908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq14544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq425
  have eq100924 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq101189 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq100924 X1 X1
       have i₂ := eq20 X1 X1 x
       grind)
    | (have i₁ := eq100924 x x
       have i₂ := eq20 x X1 x
       grind)
    | exact superpose eq20 eq100924
    | exact resolve eq100924 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151127 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14544 (τ X1) (τ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq14544
    | exact resolve eq14544 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq151530 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14544 x x
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq14544
    | exact resolve eq14544 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq151583 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq14544 X0 X1
       grind)
    | exact superpose eq14544 eq9
    | (have j1 := eq14544 X0 X1
       grind)
    | exact resolve eq9 eq14544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152242 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14544 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14544
  have eq152243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq152242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152242
  have eq152250 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) := by grind
  clear eq151530
  have eq152689 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151583 X0 X1
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq151583
    | (have j0 := eq151583 X0 X1
       grind)
    | exact resolve eq151583 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151583
  have eq152968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq151127 X0 X1
       have i₂ := eq152243 (τ X0)
       grind)
    | exact superpose eq152243 eq151127
    | (have j0 := eq151127 X0 X1
       grind)
    | exact resolve eq151127 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151127
  have eq153199 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152689 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq152689
    | (have j0 := eq152689 X0 X1
       grind)
    | exact resolve eq152689 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152689
  have eq153330 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq152968 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq152968
    | (have j0 := eq152968 X0 X1
       grind)
    | exact resolve eq152968 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152968
  have eq153503 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq153330 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153330
    | (have j0 := eq153330 X0 X1
       grind)
    | exact resolve eq153330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153330
  have eq153585 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq153503 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq153503
    | (have j0 := eq153503 X0 X1
       grind)
    | exact resolve eq153503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153503
  have eq153627 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153585 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq153585
    | (have j0 := eq153585 X0 X1
       grind)
    | exact resolve eq153585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153585
  have eq153647 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153627 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153627
    | (have j0 := eq153627 X0 X1
       grind)
    | exact resolve eq153627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153627
  have eq153652 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153647 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq153647
    | (have j0 := eq153647 X0 X1
       grind)
    | exact resolve eq153647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153647
  have eq153701 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq152243 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152243
    | exact resolve eq152243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153797 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq423
    | (have j0 := eq423 X0 X1
       grind)
    | exact resolve eq423 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq153855 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1 (σ X0)
       have i₂ := eq152243 X0
       grind)
    | exact superpose eq152243 eq20
    | exact resolve eq20 eq152243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152243
  have eq154065 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153797 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq153797
    | (have j0 := eq153797 X0 X1
       grind)
    | exact resolve eq153797 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153797
  have eq154103 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq153701 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq153701
    | exact resolve eq153701 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq153701
  have eq154139 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq154103 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154103
    | exact resolve eq154103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154103
  have eq164760 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq152250
       grind)
    | exact superpose eq152250 eq9
    | exact resolve eq9 eq152250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152250
  have eq165056 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq164760
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq164760
    | exact resolve eq164760 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164760
  have eq165155 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq165056
       have i₂ := eq154139 x
       grind)
    | exact superpose eq154139 eq165056
    | exact resolve eq165056 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165056
  have eq165156 : y = (M.op x x) := by grind
  clear eq165155
  have eq166152 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq20 x X0 x
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq20
    | exact resolve eq20 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq166156 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x X0 x
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq25
    | exact resolve eq25 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq168407 : ∀ X1 : G, (M.op x y) = (M.op x (k x X1)) ∨ (M.op x x) = X1 := by
    intro X1
    first
    | (have i₁ := eq11909 x X1 x
       have i₂ := eq166152 x
       grind)
    | exact superpose eq166152 eq11909
    | (have j0 := eq11909 x X1 x
       grind)
    | exact resolve eq11909 eq166152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11909 eq166152
  have eq168620 : ∀ X1 : G, (M.op x y) = (M.op x (k x X1)) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq168407 X1
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq168407
    | (have j0 := eq168407 X1
       grind)
    | exact resolve eq168407 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168407
  have eq172053 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq154139 X0
       have i₂ := eq153652 X0 X1
       grind)
    | (have i₁ := eq154139 X1
       have i₂ := eq153652 X1 X1
       grind)
    | exact superpose eq153652 eq154139
    | (have j1 := eq153652 X0 X1
       grind)
    | exact resolve eq154139 eq153652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq153652 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153652
  have eq172113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq172110 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq172110
    | (have j0 := eq172110 X0 X1
       grind)
    | (have r₁ := eq172110 X0 X0
       have r₂ := eq154139 X0
       grind)
    | exact resolve eq172110 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172110
  have eq172236 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq172113 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq172113
    | (have j0 := eq172113 X0 X1
       grind)
    | exact resolve eq172113 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172113
  have eq172721 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172236 x (k x X0)
       have i₂ := eq168620 X0
       grind)
    | exact superpose eq168620 eq172236
    | (have j0 := eq172236 x y
       have j1 := eq168620 X0
       grind)
    | exact resolve eq172236 eq168620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168620
  have eq172814 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x x) = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172721 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq172721
    | (have j0 := eq172721 X0
       grind)
    | exact resolve eq172721 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172721
  have eq172848 : ∀ X0 : G, y ≠ (M.op x y) ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172814 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq172814
    | (have j0 := eq172814 (k x (k x X0))
       grind)
    | exact resolve eq172814 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172814
  have eq175812 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq153855 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq153855
    | exact resolve eq153855 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153855
  have eq178962 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq175812 x X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq175812
    | exact resolve eq175812 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175812
  have eq179510 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x) X0 x
       have i₂ := eq178962 x
       grind)
    | exact superpose eq178962 eq8
    | exact resolve eq8 eq178962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179542 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101189 (σ x) x
       have i₂ := eq178962 x
       grind)
    | exact superpose eq178962 eq101189
    | exact resolve eq101189 eq178962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101189 eq178962
  have eq179791 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ (k x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq179510 (σ X0)
       have i₂ := eq154065 x X0
       grind)
    | exact superpose eq154065 eq179510
    | (have j1 := eq154065 x X0
       grind)
    | exact resolve eq179510 eq154065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154065 eq179510
  have eq180069 : ∀ X0 : G, (M.op x x) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) := by
    intro X0
    first
    | (have i₁ := eq179791 X0
       have i₂ := eq154139 x
       grind)
    | exact superpose eq154139 eq179791
    | (have j0 := eq179791 X0
       grind)
    | exact resolve eq179791 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179791
  have eq180105 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq180069 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq180069
    | (have j0 := eq180069 X0
       grind)
    | exact resolve eq180069 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180069
  have eq180183 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq44 x (M.op (σ x) (σ y))
       have i₂ := eq179542
       grind)
    | exact superpose eq179542 eq44
    | exact resolve eq44 eq179542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq179542
  have eq206172 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq180105 X0
       have i₂ := eq934 X0 x
       grind)
    | exact superpose eq934 eq180105
    | (have j0 := eq180105 X0
       have j1 := eq934 X0 x
       grind)
    | exact resolve eq180105 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934 eq180105
  have eq206301 : ∀ X0 : G, y = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq206172 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq206172
    | (have j0 := eq206172 X0
       grind)
    | exact resolve eq206172 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206172
  have eq206302 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x X0))) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq206301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206301
  have eq211105 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq153199 X0 X1
       have i₂ := eq172053 X0 X1
       grind)
    | exact superpose eq172053 eq153199
    | (have j1 := eq172053 X0 X1
       grind)
    | exact resolve eq153199 eq172053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153199 eq172053
  have eq211295 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq211105 X0 X1
       have i₂ := eq154139 X0
       grind)
    | exact superpose eq154139 eq211105
    | (have j0 := eq211105 X0 X1
       grind)
    | exact resolve eq211105 eq154139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154139 eq211105
  have eq211340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq211295 X0 X1
       have j1 := eq172236 X0 X1
       grind)
    | (have r₁ := eq211295 X0 X1
       have r₂ := eq172236 X0 X1
       grind)
    | (have r₁ := eq211295 X1 X1
       have r₂ := eq172236 X1 X1
       grind)
    | exact resolve eq211295 eq172236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172236 eq211295
  have eq225422 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x (M.op x X0))) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq206302 X0
       have i₂ := eq211340 x (M.op x X0)
       grind)
    | exact superpose eq211340 eq206302
    | (have j0 := eq206302 X0
       have j1 := eq211340 x (M.op x X0)
       grind)
    | exact resolve eq206302 eq211340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206302 eq211340
  have eq225654 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq225422 X0
       have i₂ := eq166156 X0
       grind)
    | exact superpose eq166156 eq225422
    | (have j0 := eq225422 X0
       grind)
    | exact resolve eq225422 eq166156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225422
  have eq225688 : ∀ X0 : G, y = X0 ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq225654 X0
       grind)
    | (have r₁ := eq225654 X0
       have r₂ := eq14
       grind)
    | exact resolve eq225654 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225654
  have eq225701 : ∀ X0 : G, y = (k x (M.op x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq225688 X0
       have i₂ := eq165156
       grind)
    | exact superpose eq165156 eq225688
    | (have j0 := eq225688 (k x (M.op x X0))
       grind)
    | exact resolve eq225688 eq165156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165156 eq225688
  have eq225911 : ∀ X0 : G, y = (M.op x (M.op x X0)) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq100924 x X0
       have i₂ := eq225701 (M.op x X0)
       grind)
    | exact superpose eq225701 eq100924
    | (have j1 := eq225701 (M.op x (M.op x X0))
       grind)
    | exact resolve eq100924 eq225701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100924 eq225701
  have eq225999 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq225911 X0
       have i₂ := eq166156 X0
       grind)
    | exact superpose eq166156 eq225911
    | (have j0 := eq225911 y
       grind)
    | exact resolve eq225911 eq166156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166156 eq225911
  have eq227459 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq225999 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225999
  have eq227460 : y = (M.op x y) := by grind
  clear eq227459
  have eq227560 : ∀ X0 : G, y ≠ y ∨ y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq172848 X0
       have i₂ := eq227460
       grind)
    | exact superpose eq227460 eq172848
    | (have j0 := eq172848 X0
       grind)
    | (have r₁ := eq172848 X0
       have r₂ := eq227460
       grind)
    | exact resolve eq172848 eq227460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172848
  have eq227805 : ∀ X0 : G, y = (k x (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq227560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227560
  have eq232043 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq227805 (τ (M.op (σ x) (σ y)))
       have i₂ := eq180183
       grind)
    | exact superpose eq180183 eq227805
    | (have j0 := eq227805 (k x (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq227805 eq180183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227805
  have eq232392 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq232043
       have i₂ := eq180183
       grind)
    | exact superpose eq180183 eq232043
    | exact resolve eq232043 eq180183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180183 eq232043
  have eq232393 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq232392
  have eq232536 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq232393
       grind)
    | exact superpose eq232393 eq10
    | exact resolve eq10 eq232393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232393
  have eq233361 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq232536
       grind)
    | exact superpose eq232536 eq14
    | exact resolve eq14 eq232536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232536
  have eq233687 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq233361
       have i₂ := eq227460
       grind)
    | exact superpose eq227460 eq233361
    | exact resolve eq233361 eq227460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227460 eq233361
  have eq233688 : False := by grind
  exact eq233688
