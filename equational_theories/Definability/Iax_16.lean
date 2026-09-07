import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X1 x)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq24 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq34 X2 X2
       grind)
    | exact superpose eq34 eq70
    | (have j0 := eq70 X0 X1 X2
       grind)
    | exact resolve eq70 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq70
  have eq511 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq525 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq511 X0 X1
       have j1 := eq84 X0 X1 x
       grind)
    | (have r₁ := eq511 x x
       have r₂ := eq84 x x x
       grind)
    | (have r₁ := eq511 X0 X1
       have r₂ := eq84 X0 X1 X0
       grind)
    | exact resolve eq511 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq511
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq525 (σ X0) (σ X1)
       grind)
    | exact superpose eq525 eq13
    | exact resolve eq13 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq525 X0 X1
       grind)
    | exact superpose eq525 eq554
    | exact resolve eq554 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq554
  have eq6563 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq565 x y
       grind)
    | exact superpose eq565 eq14
    | (have r₁ := eq14
       have r₂ := eq565 x y
       grind)
    | exact resolve eq14 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq6632 : False := by grind
  exact eq6632

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3274 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq156 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq156 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq156 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq179 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq160 (σ X0) (σ X1)
       grind)
    | exact superpose eq160 eq13
    | exact resolve eq13 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq179
    | exact resolve eq179 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq179
  have eq1516 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq14
    | (have r₁ := eq14
       have r₂ := eq188 x y
       grind)
    | exact resolve eq14 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1546 : False := by grind
  exact eq1546

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3284 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3284 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq260 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq266 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq260 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq260 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq260 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq266 (σ X0) (σ X1)
       grind)
    | exact superpose eq266 eq13
    | exact resolve eq13 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq266 X0 X1
       grind)
    | exact superpose eq266 eq288
    | exact resolve eq288 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq288
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq14
    | (have r₁ := eq14
       have r₂ := eq298 x y
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1173 : False := by grind
  exact eq1173

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq255 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq261 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq255 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq255 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq255 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq261 (σ X0) (σ X1)
       grind)
    | exact superpose eq261 eq13
    | exact resolve eq13 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq261 X0 X1
       grind)
    | exact superpose eq261 eq283
    | exact resolve eq283 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq283
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq293 x y
       grind)
    | exact superpose eq293 eq14
    | (have r₁ := eq14
       have r₂ := eq293 x y
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq1260 : False := by grind
  exact eq1260

/-- `Equation3309`: `x ◇ y = x ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation3309 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3309 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3309.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq89 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq89 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq13
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq109
    | exact resolve eq109 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq109
  have eq1320 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq14
    | (have r₁ := eq14
       have r₂ := eq116 x y
       grind)
    | exact resolve eq14 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1343 : False := by grind
  exact eq1343

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3317 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3317 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 x)
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq37 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq37
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (k X2 (M.op X1 X0)) ∨ (M.op X2 (M.op X0 X1)) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X1 X0) X2 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq28
    | (have j0 := eq28 X1 X2 X0
       grind)
    | exact resolve eq28 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq99 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq44
  have eq113 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 X0) X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq62 (M.op X1 X1) X1
       have r₂ := eq19 X1 X1
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq30
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq19
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq19 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq113
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq113 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq113
  have eq289 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq735 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq10
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq10 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq820 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq884 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq900 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1
       have i₂ := eq820 X0 (τ X1)
       grind)
    | (have i₁ := eq37 X0
       have i₂ := eq820 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq820 eq37
    | (have j1 := eq820 X0 (τ X1)
       grind)
    | exact resolve eq37 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq905 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq900
    | (have j0 := eq900 X0 X1
       grind)
    | exact resolve eq900 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1315 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq14
    | (have j1 := eq56 y x
       grind)
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq56 X0 X0
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X1) (σ X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq19
    | (have j1 := eq56 X0 X1
       grind)
    | exact resolve eq19 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq183 X0 X1
       grind)
    | exact superpose eq183 eq56
    | (have j0 := eq56 X1 X0
       have j1 := eq183 X0 X1
       grind)
    | exact resolve eq56 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq183
  have eq1923 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq2115 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152
    | (have j0 := eq152 X1 (τ X0)
       grind)
    | exact resolve eq152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2229 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2115 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq2115
    | (have j0 := eq2115 X0 X1
       grind)
    | exact resolve eq2115 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2239 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2229
    | (have j0 := eq2229 X0 X1
       grind)
    | exact resolve eq2229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2350 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq83 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq83
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2587 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2607 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq185 (τ X0)
       have i₂ := eq67 (τ X0) X0
       grind)
    | exact superpose eq67 eq185
    | (have j0 := eq185 (τ X0)
       have j1 := eq67 (τ X0) X0
       grind)
    | exact resolve eq185 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2648 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2607 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2607
    | (have j0 := eq2607 X0
       grind)
    | exact resolve eq2607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2660 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2587 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2587
    | (have j0 := eq2587 X0 X1
       grind)
    | exact resolve eq2587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2673 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2648 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2648
    | (have j0 := eq2648 X0
       grind)
    | exact resolve eq2648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2690 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq2673 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2673
    | (have j0 := eq2673 X0
       grind)
    | exact resolve eq2673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2704 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2690 X0
       have j1 := eq62 X0 X0
       grind)
    | (have r₁ := eq2690 X0
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq2690 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2690
  have eq2823 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2704 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2704
    | (have j0 := eq2704 (σ X0)
       grind)
    | exact resolve eq2704 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq2845 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2823 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq2823
    | (have j0 := eq2823 X0
       grind)
    | exact resolve eq2823 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq3494 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq168
    | (have j0 := eq168 (τ X0) (τ X1)
       grind)
    | exact resolve eq168 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq168
  have eq3537 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3494 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3494
    | (have j0 := eq3494 X0 X1
       grind)
    | exact resolve eq3494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq3544 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3537 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3537
    | (have j0 := eq3537 X0 X1
       grind)
    | exact resolve eq3537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3546 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3544 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3544
    | (have j0 := eq3544 X0 X1
       grind)
    | exact resolve eq3544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3547 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3546 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3546
    | (have j0 := eq3546 X0 X1
       grind)
    | exact resolve eq3546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3548 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3547 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3547
    | (have j0 := eq3547 X0 X1
       grind)
    | exact resolve eq3547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq4352 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq151 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq151 X0 X1
       grind)
    | exact superpose eq151 eq9
    | (have j1 := eq151 X0 X1
       grind)
    | exact resolve eq9 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq4405 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4352 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4352
    | (have j0 := eq4352 X0 X1
       grind)
    | exact resolve eq4352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq8155 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq289 x y
       grind)
    | exact superpose eq289 eq14
    | (have j1 := eq289 x y
       grind)
    | exact resolve eq14 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq8218 : y = (k y x) := by
    first
    | (have j1 := eq884 x y
       grind)
    | (have r₁ := eq8155
       have r₂ := eq884 x y
       grind)
    | exact resolve eq8155 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq8155
  have eq8856 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq820 x y
       have i₂ := eq8218
       grind)
    | exact superpose eq8218 eq820
    | (have j0 := eq820 x y
       grind)
    | exact resolve eq820 eq8218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8858 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3548 y x
       have i₂ := eq8218
       grind)
    | exact superpose eq8218 eq3548
    | (have j0 := eq3548 y (M.op y x)
       grind)
    | exact resolve eq3548 eq8218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq13023 : x ≠ (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq8858
  have eq24866 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq140 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq140
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq140 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq24961 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq24866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24866
  have eq26018 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq767 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq767
    | (have j0 := eq767 X1 (σ X0)
       grind)
    | exact resolve eq767 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26323 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq767 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq26324 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq26323 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26323
    | (have j0 := eq26323 X0
       grind)
    | exact resolve eq26323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26323
  have eq26365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26018 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq26018
    | (have j0 := eq26018 X0 X1
       grind)
    | exact resolve eq26018 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26018
  have eq26439 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq26324 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq26324
    | (have j0 := eq26324 (σ X0)
       grind)
    | exact resolve eq26324 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26324
  have eq26451 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26439 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq26439
    | (have j0 := eq26439 X0
       grind)
    | exact resolve eq26439 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26439
  have eq26470 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1315
       have i₂ := eq24961 x y
       grind)
    | exact superpose eq24961 eq1315
    | (have j1 := eq24961 x y
       grind)
    | exact resolve eq1315 eq24961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24961
  have eq26479 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq26470
  have eq29371 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1923 x y
       grind)
    | exact superpose eq1923 eq14
    | (have j1 := eq1923 x y
       grind)
    | exact resolve eq14 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29527 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq29371
       have i₂ := eq8218
       grind)
    | exact superpose eq8218 eq29371
    | exact resolve eq29371 eq8218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29371
  have eq29547 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq29527
       have i₂ := eq26479
       grind)
    | exact superpose eq26479 eq29527
    | (have r₁ := eq29527
       have r₂ := eq26479
       grind)
    | exact resolve eq29527 eq26479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26479 eq29527
  have eq29553 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by grind
  clear eq29547
  have eq29769 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq29553
       grind)
    | exact superpose eq29553 eq9
    | exact resolve eq9 eq29553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29553
  have eq29889 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq29769
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq29769
    | exact resolve eq29769 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29769
  have eq29890 : x = (k x y) := by grind
  clear eq29889
  have eq30258 : y = (k x x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2239 x y
       have i₂ := eq29890
       grind)
    | exact superpose eq29890 eq2239
    | (have j0 := eq2239 x y
       grind)
    | exact resolve eq2239 eq29890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq38139 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26451 X0
       have i₂ := eq2660 X0 X0
       grind)
    | exact superpose eq2660 eq26451
    | (have j0 := eq26451 X0
       have j1 := eq2660 X0 X0
       grind)
    | (have r₁ := eq26451 x
       have r₂ := eq2660 x x
       grind)
    | exact resolve eq26451 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26451
  have eq38162 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq38139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38139
  have eq39821 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38162 X1
       have i₂ := eq820 X0 X1
       grind)
    | (have i₁ := eq38162 X0
       have i₂ := eq820 (M.op X0 X0) X1
       grind)
    | exact superpose eq820 eq38162
    | (have j1 := eq820 X0 X1
       grind)
    | exact resolve eq38162 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq38162
  have eq52508 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4405 x y
       grind)
    | exact superpose eq4405 eq14
    | (have j1 := eq4405 x y
       grind)
    | exact resolve eq14 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq52839 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq39821 x y
       grind)
    | (have r₁ := eq52508
       have r₂ := eq39821 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq52508
       have r₂ := eq39821 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq52508
       have r₂ := eq39821 x y
       grind)
    | exact resolve eq52508 eq39821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39821 eq52508
  have eq53064 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1326 y y
       have i₂ := eq52839
       grind)
    | exact superpose eq52839 eq1326
    | exact resolve eq1326 eq52839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq53067 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2660 y y
       have i₂ := eq52839
       grind)
    | exact superpose eq52839 eq2660
    | exact resolve eq2660 eq52839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660 eq52839
  have eq53082 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq53067
  have eq53083 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq53064
  have eq62645 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2350 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq62646 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62645 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62645
  have eq62746 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq29890
       have i₂ := eq62646 x y
       grind)
    | exact superpose eq62646 eq29890
    | (have j1 := eq62646 x y
       grind)
    | exact resolve eq29890 eq62646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29890 eq62646
  have eq62974 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19 y x
       have i₂ := eq62746
       grind)
    | exact superpose eq62746 eq19
    | exact resolve eq19 eq62746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62746
  have eq63011 : (M.op x y) = (M.op x x) := by grind
  clear eq62974
  have eq63040 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8856
       have i₂ := eq63011
       grind)
    | exact superpose eq63011 eq8856
    | exact resolve eq8856 eq63011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8856
  have eq63170 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2845 x
       have i₂ := eq63040
       grind)
    | exact superpose eq63040 eq2845
    | (have j0 := eq2845 x
       grind)
    | exact resolve eq2845 eq63040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63241 : (σ x) = (σ (k x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq63170
       have r₂ := eq53082
       grind)
    | exact resolve eq63170 eq53082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53082 eq63170
  have eq63480 : (k x x) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq63241
       grind)
    | exact superpose eq63241 eq9
    | exact resolve eq9 eq63241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63241
  have eq63551 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq63480
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq63480
    | exact resolve eq63480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63480
  have eq63580 : x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30258
       have i₂ := eq63551
       grind)
    | exact superpose eq63551 eq30258
    | exact resolve eq30258 eq63551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30258 eq63551
  have eq63628 : x = y ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq63580
  have eq63636 : x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq63628
       have r₂ := eq13023
       grind)
    | exact resolve eq63628 eq13023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13023 eq63628
  have eq64600 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq64601 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64600 X0 X1
       have j1 := eq152 X1 X0
       grind)
    | (have r₁ := eq64600 (k X1 X1) X0
       have r₂ := eq152 X0 X1
       grind)
    | (have r₁ := eq64600 X0 (σ (k X1 X1))
       have r₂ := eq152 (σ X0) X1
       grind)
    | (have r₁ := eq64600 X1 X0
       have r₂ := eq152 X0 X1
       grind)
    | exact resolve eq64600 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq64600
  have eq67134 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq64601 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq64601 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq64601 eq16
    | (have j1 := eq64601 (τ X1) X0
       grind)
    | exact resolve eq16 eq64601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq67135 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq64601 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq64601 X0 (σ X0)
       grind)
    | exact superpose eq64601 eq9
    | (have j1 := eq64601 X1 X0
       grind)
    | exact resolve eq9 eq64601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64601
  have eq67189 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq67134 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq67134
    | (have j0 := eq67134 X0 X1
       grind)
    | exact resolve eq67134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67134
  have eq67202 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67189 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67189
    | (have j0 := eq67189 X0 X1
       grind)
    | exact resolve eq67189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67189
  have eq67351 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq67202 (τ X0) X1
       grind)
    | exact superpose eq67202 eq17
    | (have j1 := eq67202 (τ X0) X1
       grind)
    | exact resolve eq17 eq67202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq67202
  have eq69511 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq67135 (σ X0) X1
       grind)
    | exact superpose eq67135 eq13
    | (have j1 := eq67135 (σ X0) X1
       grind)
    | exact resolve eq13 eq67135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67135
  have eq69536 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69511 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69511
    | (have j0 := eq69511 X0 X1
       grind)
    | exact resolve eq69511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69511
  have eq71738 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69536 x y
       grind)
    | exact superpose eq69536 eq14
    | (have j1 := eq69536 x y
       grind)
    | exact resolve eq14 eq69536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71807 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq71738
       have i₂ := eq8218
       grind)
    | exact superpose eq8218 eq71738
    | exact resolve eq71738 eq8218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8218 eq71738
  have eq71828 : (σ y) ≠ (σ (M.op x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq71807
       have i₂ := eq63011
       grind)
    | exact superpose eq63011 eq71807
    | exact resolve eq71807 eq63011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71807
  have eq71849 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71828
       have i₂ := eq63040
       grind)
    | exact superpose eq63040 eq71828
    | (have r₁ := eq71828
       have r₂ := eq63040
       grind)
    | exact resolve eq71828 eq63040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63040
  have eq71854 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71849
  have eq71929 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq71854
       grind)
    | exact superpose eq71854 eq27
    | (have j0 := eq27 y y
       grind)
    | exact resolve eq27 eq71854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq71854
  have eq71979 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq71929
  have eq72206 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq71979
  have eq72222 : x = (M.op y y) := by
    first
    | (have r₁ := eq72206
       have r₂ := eq63636
       grind)
    | exact resolve eq72206 eq63636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63636 eq72206
  have eq72272 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq2845 y
       have i₂ := eq72222
       grind)
    | exact superpose eq72222 eq2845
    | (have j0 := eq2845 y
       grind)
    | exact resolve eq2845 eq72222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq72287 : x = (M.op y x) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq72222
       grind)
    | exact superpose eq72222 eq19
    | exact resolve eq19 eq72222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79480 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq905
    | (have j0 := eq905 X1 (σ X0)
       grind)
    | exact resolve eq905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq79556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79480 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq79480
    | (have j0 := eq79480 X0 X1
       grind)
    | exact resolve eq79480 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79480
  have eq79560 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79556 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq79556
    | (have j0 := eq79556 X0 X1
       grind)
    | exact resolve eq79556 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79556
  have eq82253 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1923 y y
       have i₂ := eq53083
       grind)
    | exact superpose eq53083 eq1923
    | (have j0 := eq1923 y y
       grind)
    | exact resolve eq1923 eq53083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923 eq53083
  have eq82278 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq82253
       have r₂ := eq72272
       grind)
    | exact resolve eq82253 eq72272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72272 eq82253
  have eq83673 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq79560 X0 X0
       grind)
    | exact superpose eq79560 eq185
    | (have j0 := eq185 X0
       have j1 := eq79560 X0 X0
       grind)
    | (have r₁ := eq185 x
       have r₂ := eq79560 x x
       grind)
    | exact resolve eq185 eq79560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79560
  have eq83718 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83673 X0
       have j1 := eq185 X0
       grind)
    | (have r₁ := eq83673 X0
       have r₂ := eq185 X0
       grind)
    | exact resolve eq83673 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83673
  have eq84002 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83718 y
       have i₂ := eq72222
       grind)
    | exact superpose eq72222 eq83718
    | (have j0 := eq83718 y
       grind)
    | exact resolve eq83718 eq72222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72222 eq83718
  have eq85358 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67351 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67351
    | exact resolve eq67351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67351
  have eq85518 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85358 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq85358
    | (have j0 := eq85358 X0 X1
       grind)
    | exact resolve eq85358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85358
  have eq85665 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1315
       have i₂ := eq85518 x y
       grind)
    | exact superpose eq85518 eq1315
    | (have j1 := eq85518 x y
       grind)
    | (have r₁ := eq1315
       have r₂ := eq85518 x y
       grind)
    | exact resolve eq1315 eq85518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq85790 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) := by grind
  clear eq85665
  have eq85824 : (σ y) = (σ (M.op x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq85790
       have i₂ := eq63011
       grind)
    | exact superpose eq63011 eq85790
    | exact resolve eq85790 eq63011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85790
  have eq85844 : x = (k y y) := by
    first
    | (have r₁ := eq85824
       have r₂ := eq71828
       grind)
    | exact resolve eq85824 eq71828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71828 eq85824
  have eq108116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k y y))) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq19 (σ y) (σ x)
       have i₂ := eq82278
       grind)
    | exact superpose eq82278 eq19
    | exact resolve eq19 eq82278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq82278
  have eq108121 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq108116
       have i₂ := eq85844
       grind)
    | exact superpose eq85844 eq108116
    | exact resolve eq108116 eq85844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108116
  have eq108142 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108121
       have i₂ := eq85844
       grind)
    | exact superpose eq85844 eq108121
    | exact resolve eq108121 eq85844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85844 eq108121
  have eq108156 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108142
       grind)
    | exact superpose eq108142 eq14
    | exact resolve eq14 eq108142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108142
  have eq108180 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108156
       have i₂ := eq63011
       grind)
    | exact superpose eq63011 eq108156
    | exact resolve eq108156 eq63011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63011 eq108156
  have eq108197 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq108180
       have i₂ := eq69536 x x
       grind)
    | exact superpose eq69536 eq108180
    | (have j1 := eq69536 x x
       grind)
    | exact resolve eq108180 eq69536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69536
  have eq108201 : x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq85518 x x
       grind)
    | (have r₁ := eq108197
       have r₂ := eq85518 x x
       grind)
    | exact resolve eq108197 eq85518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85518 eq108197
  have eq108254 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq185 x
       have i₂ := eq108201
       grind)
    | exact superpose eq108201 eq185
    | (have j0 := eq185 x
       grind)
    | exact resolve eq185 eq108201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq108309 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26365 x x
       have i₂ := eq108201
       grind)
    | exact superpose eq108201 eq26365
    | (have j0 := eq26365 x x
       grind)
    | exact resolve eq26365 eq108201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26365 eq108201
  have eq108313 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq108309
  have eq108327 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq108254
  have eq109679 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108180
       have i₂ := eq108327
       grind)
    | exact superpose eq108327 eq108180
    | exact resolve eq108180 eq108327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108180 eq108327
  have eq109791 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq109679
  have eq109842 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq109791
       have r₂ := eq108313
       grind)
    | exact resolve eq109791 eq108313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108313 eq109791
  have eq109859 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84002
       have i₂ := eq109842
       grind)
    | exact superpose eq109842 eq84002
    | (have r₁ := eq84002
       have r₂ := eq109842
       grind)
    | exact resolve eq84002 eq109842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84002
  have eq109860 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq109842
       grind)
    | exact superpose eq109842 eq9
    | exact resolve eq9 eq109842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109842
  have eq110087 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq109859
  have eq110144 : x = y := by
    first
    | (have i₁ := eq109860
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq109860
    | exact resolve eq109860 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109860
  have eq110153 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110144
       grind)
    | exact superpose eq110144 eq14
    | exact resolve eq14 eq110144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110313 : x = (M.op x x) := by
    first
    | (have i₁ := eq72287
       have i₂ := eq110144
       grind)
    | exact superpose eq110144 eq72287
    | exact resolve eq72287 eq110144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72287 eq110144
  have eq110409 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq110153
       have i₂ := eq110313
       grind)
    | exact superpose eq110313 eq110153
    | exact resolve eq110153 eq110313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110153 eq110313
  have eq110417 : False := by grind
  exact eq110417

/-- `Equation3318`: `x ◇ y = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3318 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3318 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3318.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq19 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq28
    | exact resolve eq28 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq28 (τ X0) X1
       grind)
    | exact superpose eq28 eq17
    | (have j1 := eq28 (τ X0) X1
       grind)
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq66 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq103 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq141 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq30
    | (have j0 := eq30 X0 X1
       have j1 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq30 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq30
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq103
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq103 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq103
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq251
    | (have j0 := eq251 X0 X1
       grind)
    | exact resolve eq251 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq640 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq10
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq721 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq640
    | (have j0 := eq640 X0 X1
       grind)
    | exact resolve eq640 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq744 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq788 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq744
    | (have j0 := eq744 X0 X1
       grind)
    | exact resolve eq744 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq862 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1
       have i₂ := eq721 X0 (τ X1)
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq721 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq721 eq25
    | (have j1 := eq721 X0 (τ X1)
       grind)
    | exact resolve eq25 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq869 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1058 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 y x
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq41 X0 X0
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq19
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq19 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2220 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | (have j0 := eq66 X1 (σ X0)
       grind)
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2295 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2220 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2220
    | (have j0 := eq2220 X0 X1
       grind)
    | exact resolve eq2220 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2457 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq2295 X0 X0
       grind)
    | exact superpose eq2295 eq175
    | (have j0 := eq175 X0
       have j1 := eq2295 X0 X0
       grind)
    | (have r₁ := eq175 x
       have r₂ := eq2295 x x
       grind)
    | exact resolve eq175 eq2295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2488 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq3716 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq141 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq141 X0 X1
       grind)
    | exact superpose eq141 eq9
    | (have j1 := eq141 X0 X1
       grind)
    | exact resolve eq9 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3770 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3716 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3716
    | (have j0 := eq3716 X0 X1
       grind)
    | exact resolve eq3716 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq6393 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq269 x y
       grind)
    | exact superpose eq269 eq14
    | (have j1 := eq269 x y
       grind)
    | exact resolve eq14 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq6443 : y = (k y x) := by
    first
    | (have j1 := eq788 x y
       grind)
    | (have r₁ := eq6393
       have r₂ := eq788 x y
       grind)
    | exact resolve eq6393 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6393
  have eq7030 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq721 x y
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq721
    | (have j0 := eq721 x y
       grind)
    | exact resolve eq721 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18173 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq672
    | (have j0 := eq672 X1 (σ X0)
       grind)
    | exact resolve eq672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18452 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq672 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq18453 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq18452 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18452
    | (have j0 := eq18452 X0
       grind)
    | exact resolve eq18452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18452
  have eq18493 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18173 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq18173
    | (have j0 := eq18173 X0 X1
       grind)
    | exact resolve eq18173 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173
  have eq18604 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18453 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq18453
    | (have j0 := eq18453 X0
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq18453 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq18453 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq18628 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq18604 X0
       have j1 := eq18453 X0
       grind)
    | (have r₁ := eq18604 X0
       have r₂ := eq18453 X0
       grind)
    | exact resolve eq18604 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18453 eq18604
  have eq18958 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18628 (σ X0)
       have i₂ := eq2488 X0
       grind)
    | exact superpose eq2488 eq18628
    | (have j0 := eq18628 (σ X0)
       have j1 := eq2488 X0
       grind)
    | (have r₁ := eq18628 (σ X0)
       have r₂ := eq2488 X0
       grind)
    | exact resolve eq18628 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488 eq18628
  have eq18969 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18958 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18958
  have eq18976 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18969 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq18969
    | (have j0 := eq18969 X0
       grind)
    | exact resolve eq18969 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18969
  have eq19902 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18976 X1
       have i₂ := eq721 X0 X1
       grind)
    | (have i₁ := eq18976 X0
       have i₂ := eq721 (M.op X0 X0) X1
       grind)
    | exact superpose eq721 eq18976
    | (have j1 := eq721 X0 X1
       grind)
    | exact resolve eq18976 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq18976
  have eq26534 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq869 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq869
    | (have j0 := eq869 X1 (σ X0)
       grind)
    | exact resolve eq869 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq26768 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26534 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26534
    | (have j0 := eq26534 X0 X1
       grind)
    | exact resolve eq26534 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26534
  have eq26791 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26768 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq26768
    | (have j0 := eq26768 X0 X1
       grind)
    | exact resolve eq26768 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26768
  have eq31915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq18493 x y
       grind)
    | exact superpose eq18493 eq1058
    | (have j1 := eq18493 x y
       grind)
    | (have r₁ := eq1058
       have r₂ := eq18493 x y
       grind)
    | exact resolve eq1058 eq18493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq32372 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq31915
  have eq46221 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq26791 X0 X0
       grind)
    | exact superpose eq26791 eq175
    | (have j0 := eq175 X0
       have j1 := eq26791 X0 X0
       grind)
    | (have r₁ := eq175 x
       have r₂ := eq26791 x x
       grind)
    | exact resolve eq175 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26791
  have eq46430 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq46221 X0
       have j1 := eq175 X0
       grind)
    | (have r₁ := eq46221 X0
       have r₂ := eq175 X0
       grind)
    | exact resolve eq46221 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46221
  have eq54038 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3770 x y
       grind)
    | exact superpose eq3770 eq14
    | (have j1 := eq3770 x y
       grind)
    | exact resolve eq14 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq54331 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq19902 x y
       grind)
    | (have r₁ := eq54038
       have r₂ := eq19902 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq54038
       have r₂ := eq19902 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq54038
       have r₂ := eq19902 x y
       grind)
    | exact resolve eq54038 eq19902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19902 eq54038
  have eq58649 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq58650 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq58649 X0 X1
       have j1 := eq142 X1 X0
       grind)
    | (have r₁ := eq58649 (k X1 X1) X0
       have r₂ := eq142 X0 X1
       grind)
    | (have r₁ := eq58649 X0 (σ (k X1 X1))
       have r₂ := eq142 (σ X0) X1
       grind)
    | (have r₁ := eq58649 X1 X0
       have r₂ := eq142 X0 X1
       grind)
    | exact resolve eq58649 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq58649
  have eq58735 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq58650 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq58650 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq58650 eq16
    | (have j1 := eq58650 (τ X1) X0
       grind)
    | exact resolve eq16 eq58650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq58738 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq58650 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq58650 X0 (σ X0)
       grind)
    | exact superpose eq58650 eq9
    | (have j1 := eq58650 X1 X0
       grind)
    | exact resolve eq9 eq58650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58650
  have eq58814 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq58735 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq58735
    | (have j0 := eq58735 X0 X1
       grind)
    | exact resolve eq58735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58735
  have eq58826 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58814 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58814
    | (have j0 := eq58814 X0 X1
       grind)
    | exact resolve eq58814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58814
  have eq59601 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq58738 (σ X0) X1
       grind)
    | exact superpose eq58738 eq13
    | (have j1 := eq58738 (σ X0) X1
       grind)
    | exact resolve eq13 eq58738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58738
  have eq59637 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59601 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq59601
    | (have j0 := eq59601 X0 X1
       grind)
    | exact resolve eq59601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59601
  have eq60949 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq59637 x y
       grind)
    | exact superpose eq59637 eq14
    | (have j1 := eq59637 x y
       grind)
    | exact resolve eq14 eq59637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61017 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq60949
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq60949
    | exact resolve eq60949 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443 eq60949
  have eq61074 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq61017
       have i₂ := eq7030
       grind)
    | exact superpose eq7030 eq61017
    | (have r₁ := eq61017
       have r₂ := eq7030
       grind)
    | exact resolve eq61017 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030 eq61017
  have eq61079 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq61074
  have eq61188 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq61079
       grind)
    | exact superpose eq61079 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq61079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61210 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq58826 y y
       have i₂ := eq61079
       grind)
    | exact superpose eq61079 eq58826
    | exact resolve eq58826 eq61079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58826 eq61079
  have eq61215 : x = (M.op y y) ∨ x = y := by grind
  clear eq61210
  have eq61228 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq61188
  have eq61549 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq61228
  have eq61570 : x = (M.op y y) := by
    first
    | (have r₁ := eq61549
       have r₂ := eq61215
       grind)
    | exact resolve eq61549 eq61215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61215 eq61549
  have eq61580 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19 y
       have i₂ := eq61570
       grind)
    | exact superpose eq61570 eq19
    | exact resolve eq19 eq61570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq61616 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq46430 y
       have i₂ := eq61570
       grind)
    | exact superpose eq61570 eq46430
    | (have j0 := eq46430 y
       grind)
    | exact resolve eq46430 eq61570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46430 eq61570
  have eq63716 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1064 y
       have i₂ := eq54331
       grind)
    | exact superpose eq54331 eq1064
    | exact resolve eq1064 eq54331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq54331
  have eq63725 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq63716
  have eq69492 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63725
       grind)
    | exact superpose eq63725 eq14
    | exact resolve eq14 eq63725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63725
  have eq69523 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69492
       have i₂ := eq61580
       grind)
    | exact superpose eq61580 eq69492
    | exact resolve eq69492 eq61580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69492
  have eq69540 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq69523
       have i₂ := eq59637 x x
       grind)
    | exact superpose eq59637 eq69523
    | (have j1 := eq59637 x x
       grind)
    | exact resolve eq69523 eq59637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59637
  have eq69549 : x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq788 x x
       grind)
    | (have r₁ := eq69540
       have r₂ := eq788 x x
       grind)
    | exact resolve eq69540 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq69540
  have eq69574 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq69549
       grind)
    | exact superpose eq69549 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq69549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq69620 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18493 x x
       have i₂ := eq69549
       grind)
    | exact superpose eq69549 eq18493
    | (have j0 := eq18493 x x
       grind)
    | exact resolve eq18493 eq69549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18493 eq69549
  have eq69624 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq69620
  have eq69637 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq69574
  have eq70677 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69523
       have i₂ := eq69637
       grind)
    | exact superpose eq69637 eq69523
    | exact resolve eq69523 eq69637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69523 eq69637
  have eq70776 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq70677
  have eq70815 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq70776
       have r₂ := eq69624
       grind)
    | exact resolve eq70776 eq69624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69624 eq70776
  have eq70843 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq70815
       grind)
    | exact superpose eq70815 eq14
    | exact resolve eq14 eq70815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61616
       have i₂ := eq70815
       grind)
    | exact superpose eq70815 eq61616
    | (have r₁ := eq61616
       have r₂ := eq70815
       grind)
    | exact resolve eq61616 eq70815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61616
  have eq70849 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq70815
       grind)
    | exact superpose eq70815 eq9
    | exact resolve eq9 eq70815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70815
  have eq71088 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70847
  have eq71111 : x = y := by
    first
    | (have i₁ := eq70849
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70849
    | exact resolve eq70849 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70849
  have eq71112 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq70843
       have i₂ := eq71088
       grind)
    | exact superpose eq71088 eq70843
    | exact resolve eq70843 eq71088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70843 eq71088
  have eq71115 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq71112
       have i₂ := eq61580
       grind)
    | exact superpose eq61580 eq71112
    | exact resolve eq71112 eq61580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61580 eq71112
  have eq71146 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq32372
       have i₂ := eq71111
       grind)
    | exact superpose eq71111 eq32372
    | exact resolve eq32372 eq71111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32372 eq71111
  have eq71225 : (σ x) = (σ (M.op x x)) := by grind
  clear eq71146
  have eq71240 : False := by grind
  exact eq71240

/-- `Equation3320`: `x ◇ y = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation3320 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3320 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3320.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 x)
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 X1
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq37 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq43 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq48 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43
    | exact resolve eq43 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq78 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq48 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq48
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X1 X1) X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq73
    | (have j0 := eq73 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq73 (M.op X1 X1) X1
       have r₂ := eq19 X1 X1
       grind)
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq37
    | (have j0 := eq37 X0 X1
       have j1 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq9
    | (have j1 := eq37 X1 X0
       grind)
    | exact resolve eq9 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X2) X1
       have i₂ := eq37 X0 X2
       grind)
    | exact superpose eq37 eq19
    | (have j1 := eq37 X0 X2
       grind)
    | exact resolve eq19 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq534 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq32 X1 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq32 X0 X0 X2
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq32 X2 X1 X0
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1327 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50
    | exact resolve eq50 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1439 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1327 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1327
    | (have j0 := eq1327 X0 X1
       grind)
    | exact resolve eq1327 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1515 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1912 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq67 X0 X0
       grind)
    | exact superpose eq67 eq19
    | (have j1 := eq67 X0 X0
       grind)
    | exact resolve eq19 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2917 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq188 x X0 y
       grind)
    | exact superpose eq188 eq14
    | (have j1 := eq188 y X0 x
       grind)
    | exact resolve eq14 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq3209 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78
    | (have j0 := eq78 X1 (σ X0)
       grind)
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3287 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3209 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq3209
    | (have j0 := eq3209 X0 X1
       grind)
    | exact resolve eq3209 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3209
  have eq3554 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq193 X0
       have i₂ := eq3287 X0 X0
       grind)
    | exact superpose eq3287 eq193
    | (have j0 := eq193 X0
       have j1 := eq3287 X0 X0
       grind)
    | (have r₁ := eq193 x
       have r₂ := eq3287 x x
       grind)
    | exact resolve eq193 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq3589 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3554 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq4381 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq159 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq9
    | (have j1 := eq159 X0 X1
       grind)
    | exact resolve eq9 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq4431 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4381 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq4381
    | (have j0 := eq4381 X0 X1
       grind)
    | exact resolve eq4381 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq27883 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1 X1
       have i₂ := eq1439 X0 X1
       grind)
    | (have i₁ := eq148 X0 X1
       have i₂ := eq1439 (M.op X0 X1) X1
       grind)
    | exact superpose eq1439 eq148
    | (have j1 := eq1439 X0 X1
       grind)
    | (have r₁ := eq148 X1 X1
       have r₂ := eq1439 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq148 X0 X1
       have r₂ := eq1439 (M.op X0 X1) X1
       grind)
    | exact resolve eq148 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27885 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq148 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq148
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq148 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq148 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28015 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq148 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq28031 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27885 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27885
  have eq28033 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27883
  have eq28157 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq28015 (σ X0)
       grind)
    | exact superpose eq28015 eq47
    | exact resolve eq47 eq28015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq28015
  have eq30515 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1366 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366
  have eq30516 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq30515 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30515
    | (have j0 := eq30515 X0
       grind)
    | exact resolve eq30515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30515
  have eq30743 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq30516 X0
       have i₂ := eq28031 X0 X0
       grind)
    | exact superpose eq28031 eq30516
    | (have j0 := eq30516 X0
       have j1 := eq28031 X0 X0
       grind)
    | (have r₁ := eq30516 x
       have r₂ := eq28031 x x
       grind)
    | exact resolve eq30516 eq28031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq30763 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30516 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq30516
    | (have j0 := eq30516 (σ X0)
       grind)
    | exact resolve eq30516 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30777 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30763 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30763
    | (have j0 := eq30763 X0
       grind)
    | exact resolve eq30763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30763
  have eq30782 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq30743 X0
       have j1 := eq30516 X0
       grind)
    | (have r₁ := eq30743 X0
       have r₂ := eq30516 X0
       grind)
    | exact resolve eq30743 eq30516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30516 eq30743
  have eq31093 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30782 (σ X0)
       have i₂ := eq3589 X0
       grind)
    | exact superpose eq3589 eq30782
    | (have j0 := eq30782 (σ X0)
       have j1 := eq3589 X0
       grind)
    | (have r₁ := eq30782 (σ X0)
       have r₂ := eq3589 X0
       grind)
    | exact resolve eq30782 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589 eq30782
  have eq31099 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq31093 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31093
  have eq31104 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq31099 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31099
    | (have j0 := eq31099 X0
       grind)
    | exact resolve eq31099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099
  have eq34145 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31104 X1
       have i₂ := eq1439 X0 X1
       grind)
    | (have i₁ := eq31104 X0
       have i₂ := eq1439 (M.op X0 X0) X1
       grind)
    | exact superpose eq1439 eq31104
    | (have j1 := eq1439 X0 X1
       grind)
    | exact resolve eq31104 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439 eq31104
  have eq40317 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28157 X0
       have i₂ := eq178 X0 X1
       grind)
    | (have i₁ := eq28157 X0
       have i₂ := eq178 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq178 eq28157
    | (have j1 := eq178 X1 X0
       grind)
    | exact resolve eq28157 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq28157
  have eq51800 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq534 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq51801 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51800 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51800
  have eq52236 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2917 X0
       have i₂ := eq51801 y x
       grind)
    | exact superpose eq51801 eq2917
    | (have j0 := eq2917 X0
       have j1 := eq51801 y x
       grind)
    | exact resolve eq2917 eq51801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917 eq51801
  have eq52241 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq52236 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52236
  have eq55177 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52241 (σ x)
       grind)
    | exact superpose eq52241 eq14
    | exact resolve eq14 eq52241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52241
  have eq57947 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40317 x y
       grind)
    | exact superpose eq40317 eq14
    | (have j1 := eq40317 x y
       grind)
    | exact resolve eq14 eq40317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58110 : x = (k x y) := by
    first
    | (have j1 := eq28033 x y
       grind)
    | (have r₁ := eq57947
       have r₂ := eq28033 x y
       grind)
    | exact resolve eq57947 eq28033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28033 eq57947
  have eq58884 : x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq58110
       grind)
    | exact superpose eq58110 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq58110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58110
  have eq59366 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq58884
       grind)
    | exact superpose eq58884 eq8
    | exact resolve eq8 eq58884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63718 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq59366 X0
       have i₂ := eq58884
       grind)
    | exact superpose eq58884 eq59366
    | exact resolve eq59366 eq58884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58884 eq59366
  have eq63966 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq63718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63718
  have eq64787 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq63966 X1
       grind)
    | exact superpose eq63966 eq19
    | (have j1 := eq63966 X0
       grind)
    | exact resolve eq19 eq63966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq63966
  have eq69653 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq64787 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64787
  have eq69654 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq69653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69653
  have eq70468 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq69654 X0
       grind)
    | exact superpose eq69654 eq73
    | (have j0 := eq73 y X0
       grind)
    | exact resolve eq73 eq69654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq74890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4431 x y
       grind)
    | exact superpose eq4431 eq14
    | (have j1 := eq4431 x y
       grind)
    | exact resolve eq14 eq4431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4431
  have eq74898 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq34145 x y
       grind)
    | (have r₁ := eq74890
       have r₂ := eq34145 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq74890
       have r₂ := eq34145 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq74890
       have r₂ := eq34145 x y
       grind)
    | exact resolve eq74890 eq34145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34145 eq74890
  have eq74946 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1912 y x
       have i₂ := eq74898
       grind)
    | exact superpose eq74898 eq1912
    | exact resolve eq1912 eq74898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912 eq74898
  have eq74989 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq74946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74946
  have eq75448 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74989 (σ x)
       grind)
    | exact superpose eq74989 eq14
    | exact resolve eq14 eq74989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74989
  have eq75450 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75448
       have i₂ := eq69654 x
       grind)
    | exact superpose eq69654 eq75448
    | exact resolve eq75448 eq69654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75448
  have eq76222 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq55177
       have i₂ := eq40317 x x
       grind)
    | exact superpose eq40317 eq55177
    | (have j1 := eq40317 x x
       grind)
    | exact resolve eq55177 eq40317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76237 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq76222
       have i₂ := eq69654 x
       grind)
    | exact superpose eq69654 eq76222
    | exact resolve eq76222 eq69654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76222
  have eq76242 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq1515 x x
       grind)
    | (have r₁ := eq76237
       have r₂ := eq1515 x x
       grind)
    | exact resolve eq76237 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76237
  have eq76282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq76242
       grind)
    | exact superpose eq76242 eq193
    | (have j0 := eq193 x
       grind)
    | exact resolve eq193 eq76242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76298 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq30777 x
       have i₂ := eq76242
       grind)
    | exact superpose eq76242 eq30777
    | (have j0 := eq30777 x
       grind)
    | exact resolve eq30777 eq76242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76242
  have eq76322 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by grind
  clear eq76298
  have eq76330 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq76282
  have eq77324 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq55177
       have i₂ := eq76330
       grind)
    | exact superpose eq76330 eq55177
    | exact resolve eq55177 eq76330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55177 eq76330
  have eq77401 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by grind
  clear eq77324
  have eq77424 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq77401
       have i₂ := eq69654 x
       grind)
    | exact superpose eq69654 eq77401
    | exact resolve eq77401 eq69654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77401
  have eq77431 : x = (M.op y x) := by
    first
    | (have r₁ := eq77424
       have r₂ := eq76322
       grind)
    | exact resolve eq77424 eq76322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76322 eq77424
  have eq77469 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq70468 y
       have i₂ := eq77431
       grind)
    | exact superpose eq77431 eq70468
    | (have j0 := eq70468 y
       grind)
    | exact resolve eq70468 eq77431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70468
  have eq79126 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq75450
       have i₂ := eq40317 x x
       grind)
    | exact superpose eq40317 eq75450
    | (have j1 := eq40317 x x
       grind)
    | exact resolve eq75450 eq40317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40317
  have eq79135 : x = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1515 x x
       grind)
    | (have r₁ := eq79126
       have r₂ := eq1515 x x
       grind)
    | exact resolve eq79126 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515 eq79126
  have eq79251 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq79135
       grind)
    | exact superpose eq79135 eq193
    | (have j0 := eq193 x
       grind)
    | exact resolve eq193 eq79135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79271 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30777 x
       have i₂ := eq79135
       grind)
    | exact superpose eq79135 eq30777
    | (have j0 := eq30777 x
       grind)
    | exact resolve eq30777 eq79135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30777 eq79135
  have eq79295 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq79271
  have eq79303 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq79251
  have eq79851 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75450
       have i₂ := eq79303
       grind)
    | exact superpose eq79303 eq75450
    | exact resolve eq75450 eq79303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75450 eq79303
  have eq79931 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq79851
  have eq79959 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq79931
       have r₂ := eq79295
       grind)
    | exact resolve eq79931 eq79295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79295 eq79931
  have eq80002 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79959
       grind)
    | exact superpose eq79959 eq14
    | exact resolve eq14 eq79959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80009 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq79959
       grind)
    | exact superpose eq79959 eq9
    | exact resolve eq9 eq79959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79959
  have eq80150 : x = y := by
    first
    | (have i₁ := eq80009
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq80009
    | exact resolve eq80009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80009
  have eq80151 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq80002
       have i₂ := eq69654 x
       grind)
    | exact superpose eq69654 eq80002
    | exact resolve eq80002 eq69654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69654 eq80002
  have eq80233 : x = (M.op x x) := by
    first
    | (have i₁ := eq77431
       have i₂ := eq80150
       grind)
    | exact superpose eq80150 eq77431
    | exact resolve eq77431 eq80150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77431
  have eq80239 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq77469
       have i₂ := eq80150
       grind)
    | exact superpose eq80150 eq77469
    | (have r₁ := eq77469
       have r₂ := eq80150
       grind)
    | exact resolve eq77469 eq80150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77469 eq80150
  have eq80246 : x = (k x x) := by grind
  clear eq80239
  have eq80446 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq80246
       grind)
    | exact superpose eq80246 eq193
    | (have j0 := eq193 x
       grind)
    | exact resolve eq193 eq80246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq80246
  have eq80502 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq80446
  have eq84915 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq80151
       have i₂ := eq80502
       grind)
    | exact superpose eq80502 eq80151
    | exact resolve eq80151 eq80502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80151 eq80502
  have eq84938 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq84915
       have i₂ := eq80233
       grind)
    | exact superpose eq80233 eq84915
    | exact resolve eq84915 eq80233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80233 eq84915
  have eq84939 : False := by grind
  exact eq84939
