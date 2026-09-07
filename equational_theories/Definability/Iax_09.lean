import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation882 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq112 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq96 (σ X1) (σ X0)
       grind)
    | exact superpose eq96 eq13
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq112
    | exact resolve eq112 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq112
  have eq1272 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119 x y
       grind)
    | exact superpose eq119 eq14
    | (have r₁ := eq14
       have r₂ := eq119 x y
       grind)
    | exact resolve eq14 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1298 : False := by grind
  exact eq1298

/-- `Equation883`: `x = y ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation883 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law883 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law883.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq13
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq112
    | exact resolve eq112 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq112
  have eq1004 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119 x y
       grind)
    | exact superpose eq119 eq14
    | (have r₁ := eq14
       have r₂ := eq119 x y
       grind)
    | exact resolve eq14 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1030 : False := by grind
  exact eq1030

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation887 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X0 X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X1
       have i₂ := eq19 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq21 (M.op X1 X1) X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X0) X1
       have i₂ := eq23 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq297 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 (M.op X1 X1) X0
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq104
    | (have j0 := eq104 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq104 (M.op X0 X0) X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq104 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq104
  have eq372 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq403 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq19
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq492 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq372 (σ X0) X1
       grind)
    | exact superpose eq372 eq46
    | exact resolve eq46 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq493 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq372 (τ X0) X1
       grind)
    | exact superpose eq372 eq17
    | exact resolve eq17 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq494 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq495 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq492
    | exact resolve eq492 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1170 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq446 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq446
    | (have j0 := eq446 (τ X0)
       grind)
    | exact resolve eq446 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq446
  have eq1180 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1170 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1170
    | (have j0 := eq1170 X0
       grind)
    | exact resolve eq1170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1185 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1180 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1180
    | (have j0 := eq1180 X0
       grind)
    | exact resolve eq1180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq2364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq403
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq403
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq2375 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2364
  have eq3120 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq419 (τ X0) (τ X1)
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq419
    | (have j0 := eq419 (τ X0) (τ X1)
       grind)
    | exact resolve eq419 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq419
  have eq3311 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3120 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3120
    | (have j0 := eq3120 X0 X1
       grind)
    | exact resolve eq3120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3338 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3311 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3311
    | (have j0 := eq3311 X0 X1
       grind)
    | exact resolve eq3311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3344 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3338
    | (have j0 := eq3338 X0 X1
       grind)
    | exact resolve eq3338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3349 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3344
    | (have j0 := eq3344 X0 X1
       grind)
    | exact resolve eq3344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3350 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3349 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3349
    | (have j0 := eq3349 X0 X1
       grind)
    | exact resolve eq3349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3713 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 X2
       have i₂ := eq3350 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq3350 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3350 eq23
    | (have j1 := eq3350 X2 X0
       grind)
    | exact resolve eq23 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (M.op X0 (k X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 X1
       grind)
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3350 eq91
    | (have j1 := eq3350 X1 X0
       grind)
    | exact resolve eq91 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3350
  have eq4679 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3713 X1 X2 X0
       grind)
    | exact superpose eq3713 eq19
    | (have j1 := eq3713 X1 X2 X2
       grind)
    | exact resolve eq19 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq5729 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3723 X1 X0 X2
       grind)
    | exact superpose eq3723 eq19
    | (have j1 := eq3723 X1 X1 X2
       grind)
    | exact resolve eq19 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3723
  have eq7684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4679 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq7685 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7684 X0
       have j1 := eq5729 X0 X0 x
       grind)
    | (have r₁ := eq7684 x
       have r₂ := eq5729 X0 x x
       grind)
    | exact resolve eq7684 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729 eq7684
  have eq8009 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq7685 X0
       grind)
    | exact superpose eq7685 eq21
    | exact resolve eq21 eq7685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685
  have eq8848 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X0 X0) X1 X2
       have i₂ := eq8009 X0
       grind)
    | exact superpose eq8009 eq18
    | exact resolve eq18 eq8009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8895 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8848 X0 X1 x
       have i₂ := eq24 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq24 eq8848
    | exact resolve eq8848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8848
  have eq9771 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X1
       have i₂ := eq8895 X1 X0
       grind)
    | exact superpose eq8895 eq1185
    | (have j0 := eq1185 X1
       grind)
    | (have r₁ := eq1185 (M.op X1 X1)
       have r₂ := eq8895 (M.op X1 X1) X1
       grind)
    | exact resolve eq1185 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq9825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 (σ (M.op X1 X1)) X1
       have i₂ := eq8895 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq494
    | exact resolve eq494 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq9832 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 (τ (M.op X1 X1)) X1
       have i₂ := eq8895 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq495
    | exact resolve eq495 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq12480 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9832 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9832
    | exact resolve eq9832 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12577 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9825 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9825
    | exact resolve eq9825 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq12582 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X1
       have i₂ := eq9832 X1 X0
       grind)
    | exact superpose eq9832 eq21
    | exact resolve eq21 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq18918 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12582 (τ (M.op X0 X0)) X1
       have i₂ := eq12582 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq12582 eq12582
    | exact resolve eq12582 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12582
  have eq27584 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq495 X0 (σ x)
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq495
    | exact resolve eq495 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq2375
  have eq27665 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq27584 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27584
    | exact resolve eq27584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27584
  have eq32502 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8009 y
       have i₂ := eq27665 y
       grind)
    | exact superpose eq27665 eq8009
    | exact resolve eq8009 eq27665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009 eq27665
  have eq32571 : y = (M.op y y) := by
    first
    | (have j1 := eq9771 x y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 y y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 x y
       grind)
    | exact resolve eq32502 eq9771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq32502
  have eq32588 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq23
    | exact resolve eq23 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq32592 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq39 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq39
    | exact resolve eq39 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq32613 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq9832 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq9832
    | exact resolve eq9832 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9832
  have eq32624 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq12480 y X0
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq12480
    | exact resolve eq12480 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12480 eq32571
  have eq33072 : ∀ X0 : G, y = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18918 X0 y
       have i₂ := eq32588 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq32588 eq18918
    | exact resolve eq18918 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18918
  have eq33077 : y = (τ (τ y)) := by
    first
    | (have i₁ := eq33072 x
       have i₂ := eq32624 x
       grind)
    | exact superpose eq32624 eq33072
    | exact resolve eq33072 eq32624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624 eq33072
  have eq33937 : ∀ X0 : G, (σ y) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12577 X0 x
       have i₂ := eq32592 x
       grind)
    | exact superpose eq32592 eq12577
    | exact resolve eq12577 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577 eq32592
  have eq34116 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq33937 x
       have i₂ := eq32613 x
       grind)
    | exact superpose eq32613 eq33937
    | exact resolve eq33937 eq32613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32613 eq33937
  have eq34172 : y = (σ y) := by
    first
    | (have i₁ := eq34116
       have i₂ := eq33077
       grind)
    | exact superpose eq33077 eq34116
    | exact resolve eq34116 eq33077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33077 eq34116
  have eq34709 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34172
       grind)
    | exact superpose eq34172 eq14
    | exact resolve eq14 eq34172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34172
  have eq34816 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq34709
       have i₂ := eq32588 (σ x)
       grind)
    | exact superpose eq32588 eq34709
    | exact resolve eq34709 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34709
  have eq34845 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34816
       have i₂ := eq32588 x
       grind)
    | exact superpose eq32588 eq34816
    | exact resolve eq34816 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32588 eq34816
  have eq34846 : False := by grind
  exact eq34846

/-- `Equation895`: `x = y ◇ ((x ◇ z) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation895 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law895 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law895.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X3) (M.op X2 X3))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq66 X1 (M.op X0 X1)
       grind)
    | exact superpose eq66 eq8
    | exact resolve eq8 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (M.op X0 X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq82
    | exact resolve eq82 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq82
    | exact resolve eq82 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq173 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq114
    | exact resolve eq114 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 X1) X0) ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X2 (M.op X0 X1) (M.op X2 X1)
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq29
    | (have j0 := eq29 X2 X1 (M.op X2 X1)
       grind)
    | exact resolve eq29 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq250 : ∀ X1 X2 : G, (M.op X2 X1) = X1 ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq209 x X1 X2
       have i₂ := eq114 x X1
       grind)
    | exact superpose eq114 eq209
    | (have j0 := eq209 x X1 X2
       grind)
    | exact resolve eq209 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq262 : ∀ X1 X2 : G, (k (M.op X2 X1) X2) = X1 ∨ (M.op X2 X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq250 X1 X2
       have i₂ := eq114 X2 X1
       grind)
    | exact superpose eq114 eq250
    | (have j0 := eq250 X1 X2
       grind)
    | exact resolve eq250 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq288 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq115 (M.op X0 X1) X1
       grind)
    | exact superpose eq115 eq8
    | exact resolve eq8 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1 (M.op X1 X0)
       have i₂ := eq288 X1 X0
       grind)
    | exact superpose eq288 eq114
    | exact resolve eq114 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq288
  have eq541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  clear eq31
  have eq810 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X1) X0
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq47
    | (have j0 := eq47 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq47 (M.op X1 X1) X0
       have r₂ := eq115 X0 X1
       grind)
    | exact resolve eq47 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq814 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq841 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X1) X0
       have i₂ := eq814 (σ X0) X1
       grind)
    | exact superpose eq814 eq24
    | exact resolve eq24 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq814 (τ X0) X1
       grind)
    | exact superpose eq814 eq17
    | exact resolve eq17 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq843 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq842
    | exact resolve eq842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq841
    | exact resolve eq841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq846 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq262 (M.op X0 X0) X1
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq262
    | exact resolve eq262 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq900 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq843 (τ X0) X1
       grind)
    | exact superpose eq843 eq17
    | exact resolve eq17 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq900
    | exact resolve eq900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1103 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (τ (M.op X1 X1)) X0
       have i₂ := eq844 (σ X0) X1
       grind)
    | exact superpose eq844 eq24
    | exact resolve eq24 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1106 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1103
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1234 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq901 (τ X0) X1
       grind)
    | exact superpose eq901 eq17
    | exact resolve eq17 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1235 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1234
    | exact resolve eq1234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq541
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2943 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2942
  have eq103855 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 (σ (M.op X1 X1)) X1
       have i₂ := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq843
    | (have j1 := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact resolve eq843 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq103856 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq901
    | (have j1 := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact resolve eq901 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq103857 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) ∨ (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1235 (σ (σ (σ (M.op X1 X1)))) X1
       have i₂ := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact superpose eq846 eq1235
    | (have j1 := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact resolve eq1235 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq103862 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (τ (M.op X1 X1)) X1
       have i₂ := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq844
    | (have j1 := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact resolve eq844 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq103863 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (τ (τ (M.op X1 X1))) X1
       have i₂ := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq1106
    | (have j1 := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact resolve eq1106 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq103866 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq846 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq103869 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103863
  have eq103870 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103862
  have eq103872 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq103857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103857
  have eq103873 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103856
  have eq103874 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103855
  have eq108069 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq103870 x X2
       have i₂ := eq103874 x X0
       grind)
    | exact superpose eq103874 eq103870
    | exact resolve eq103870 eq103874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119818 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq108069 x X2
       have i₂ := eq103873 x X0
       grind)
    | exact superpose eq103873 eq108069
    | exact resolve eq108069 eq103873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103873 eq108069
  have eq125263 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103866 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq103866
    | (have j0 := eq103866 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq103866 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq103866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq125285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq125263 X0 X1
       have j1 := eq103866 X1 X0
       grind)
    | (have r₁ := eq125263 X1 X1
       have r₂ := eq103866 X1 X1
       grind)
    | (have r₁ := eq125263 (M.op X0 X0) X1
       have r₂ := eq103866 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq125263 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq103866 X0 (M.op X1 X1)
       grind)
    | exact resolve eq125263 eq103866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103866 eq125263
  have eq125646 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X0 X1
       grind)
    | exact superpose eq173 eq125285
    | (have j0 := eq125285 X1 X2
       grind)
    | (have r₁ := eq125285 (M.op X1 X1) X1
       have r₂ := eq173 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq125285 (M.op X0 X0) X1
       have r₂ := eq173 X0 (M.op X0 X0)
       grind)
    | exact resolve eq125285 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq125285
  have eq128311 : ∀ X0 X2 X3 : G, (σ (σ (σ (M.op X0 X0)))) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq125646 x X2 X3
       have i₂ := eq103872 x X0
       grind)
    | exact superpose eq103872 eq125646
    | (have j0 := eq125646 X0 X2 X3
       grind)
    | (have r₁ := eq125646 X0 (σ (σ (σ (M.op x x)))) X2
       have r₂ := eq103872 X0 x
       grind)
    | exact resolve eq125646 eq103872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103872 eq125646
  have eq147851 : ∀ X0 : G, (σ (σ (σ (M.op X0 X0)))) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119818 X0 (σ x)
       have i₂ := eq2943
       grind)
    | exact superpose eq2943 eq119818
    | exact resolve eq119818 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943 eq119818
  have eq147954 : ∀ X0 : G, y = (σ (σ (σ (M.op X0 X0)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq147851 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq147851
    | exact resolve eq147851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147851
  have eq147995 : y = (M.op x x) := by
    first
    | (have j1 := eq128311 x y x
       grind)
    | (have r₁ := eq147954 x
       have r₂ := eq128311 x y x
       grind)
    | exact resolve eq147954 eq128311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128311 eq147954
  have eq148007 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 x X0
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq66
    | exact resolve eq66 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq148009 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq115
    | exact resolve eq115 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq148027 : ∀ X0 : G, (M.op X0 X0) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq103869 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103869
    | exact resolve eq103869 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103869
  have eq148028 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq103870 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103870
    | exact resolve eq103870 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103870
  have eq148032 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq103874 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103874
    | exact resolve eq103874 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103874 eq147995
  have eq148240 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq148028 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148028
    | exact resolve eq148028 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148028
  have eq148241 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq148027 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148027
    | exact resolve eq148027 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148027 eq148032
  have eq148289 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq148241
       have i₂ := eq148240
       grind)
    | exact superpose eq148240 eq148241
    | exact resolve eq148241 eq148240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148240 eq148241
  have eq148321 : y = (σ y) := by
    first
    | (have i₁ := eq148289
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq148289
    | exact resolve eq148289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148289
  have eq148502 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq148321
       grind)
    | exact superpose eq148321 eq14
    | exact resolve eq14 eq148321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148321
  have eq148546 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq148502
       have i₂ := eq498 (σ x) y
       grind)
    | (have i₁ := eq148502
       have i₂ := eq498 y (σ x)
       grind)
    | exact superpose eq498 eq148502
    | exact resolve eq148502 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq148502
  have eq148561 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq148546
       have i₂ := eq148009 (σ x)
       grind)
    | exact superpose eq148009 eq148546
    | exact resolve eq148546 eq148009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148009 eq148546
  have eq148568 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq148561
       have i₂ := eq148007 x
       grind)
    | exact superpose eq148007 eq148561
    | exact resolve eq148561 eq148007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148007 eq148561
  have eq148569 : False := by grind
  exact eq148569

/-- `Equation898`: `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation898 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law898 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law898.models_iff G M).mp hM
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq127 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq127 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq127 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq131 (σ X0) (σ X1)
       grind)
    | exact superpose eq131 eq13
    | exact resolve eq13 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq150
    | exact resolve eq150 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq150
  have eq763 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq159 x y
       grind)
    | exact superpose eq159 eq14
    | (have r₁ := eq14
       have r₂ := eq159 x y
       grind)
    | exact resolve eq14 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq789 : False := by grind
  exact eq789

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation907 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law907 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact superpose eq97 eq13
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq113
    | exact resolve eq113 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq113
  have eq1105 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq14
    | (have r₁ := eq14
       have r₂ := eq120 x y
       grind)
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1132 : False := by grind
  exact eq1132

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_x_pxy_Equation916 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law916 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
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
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq11 X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq50 X0 (τ X1)
       grind)
    | exact superpose eq50 eq16
    | (have j1 := eq50 X0 (τ X1)
       grind)
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq89 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq30 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq104 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq70
    | (have j0 := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq70 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq70
    | (have j0 := eq70 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq91 X0
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq138 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27 X0 (M.op (σ X0) (M.op (σ X0) (σ X0)))
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq27
    | exact resolve eq27 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq110
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq138
    | exact resolve eq138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq496 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq701 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq94
    | exact resolve eq94 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq41
    | exact resolve eq41 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq727 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq720 X0 x X2
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq720
    | (have j0 := eq720 X0 x X2
       grind)
    | exact resolve eq720 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq733 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq701 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq701
    | exact resolve eq701 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq739 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq733 X0
       have i₂ := eq21 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq733
    | exact resolve eq733 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq742 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq739
    | exact resolve eq739 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq750 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq742 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq742
    | exact resolve eq742 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq44
    | exact resolve eq44 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq770 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq750
    | exact resolve eq750 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq776 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq95 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq95 eq94
    | exact resolve eq94 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq806 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq794
    | exact resolve eq794 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq810 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq776
    | exact resolve eq776 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq885 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq8
    | exact resolve eq8 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (M.op X0 (M.op X0 X0))
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq91
    | exact resolve eq91 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq924 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq895
    | exact resolve eq895 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq942 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64 x y
       grind)
    | exact superpose eq64 eq14
    | (have j1 := eq64 x y
       grind)
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | exact resolve eq11 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq977 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq967
    | (have j0 := eq967 X0 X1
       grind)
    | exact resolve eq967 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq978 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq977 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1030 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq810
    | exact resolve eq810 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))
       have i₂ := eq810 X0 X1
       grind)
    | exact superpose eq810 eq12
    | exact resolve eq12 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq1073
    | (have j0 := eq1073 X0 X1
       grind)
    | exact resolve eq1073 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1107 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1172 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq885
    | exact resolve eq885 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq91
    | exact resolve eq91 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq94
    | exact resolve eq94 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1203 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq810
    | exact resolve eq810 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (M.op (M.op X0 X0) (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq885 (σ X1) X0
       grind)
    | exact superpose eq885 eq142
    | exact resolve eq142 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1278 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1278
    | (have j0 := eq1278 X0 X1
       grind)
    | exact resolve eq1278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1398 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq1195
    | exact resolve eq1195 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1195 x (M.op X0 X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq1195
    | exact resolve eq1195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq2708 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1398 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1398
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq1398 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq2806 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2708 X0 X1
       have i₂ := eq924 X0
       grind)
    | exact superpose eq924 eq2708
    | (have j0 := eq2708 X0 X1
       grind)
    | exact resolve eq2708 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq2708
  have eq3242 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 (τ X0) (τ X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq496
    | (have j0 := eq496 (τ X0) (τ X1)
       grind)
    | exact resolve eq496 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq3268 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3242
    | (have j0 := eq3242 X0 X1
       grind)
    | exact resolve eq3242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3273 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3268 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3268
    | (have j0 := eq3268 X0 X1
       grind)
    | exact resolve eq3268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3276 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3273 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3273
    | (have j0 := eq3273 X0 X1
       grind)
    | exact resolve eq3273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3277 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3276
    | (have j0 := eq3276 X0 X1
       grind)
    | exact resolve eq3276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3544 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3277 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq810 X1 X1
       grind)
    | exact superpose eq810 eq3277
    | exact resolve eq3277 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq3277
  have eq4834 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 X0) (M.op X1 (M.op X1 X1))
       have i₂ := eq1030 X0 X1
       grind)
    | exact superpose eq1030 eq1030
    | exact resolve eq1030 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5107 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4834 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq4834
    | exact resolve eq4834 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq4834
  have eq5220 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5107 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq5107
    | exact resolve eq5107 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5267 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5220 X0 X1
       have i₂ := eq770 X1
       grind)
    | exact superpose eq770 eq5220
    | exact resolve eq5220 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq12505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq942
       have i₂ := eq872 y x
       grind)
    | exact superpose eq872 eq942
    | (have j1 := eq872 y x
       grind)
    | (have r₁ := eq942
       have r₂ := eq872 y x
       grind)
    | exact resolve eq942 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq942
  have eq12506 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq12505
  have eq12576 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq12506
       grind)
    | exact superpose eq12506 eq9
    | exact resolve eq9 eq12506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12631 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12576
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12576
    | exact resolve eq12576 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576
  have eq12632 : x = (k x y) := by
    first
    | (have j1 := eq70 x y
       grind)
    | (have r₁ := eq12631
       have r₂ := eq70 x y
       grind)
    | exact resolve eq12631 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq12631
  have eq18687 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq1107
    | (have j0 := eq1107 (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) X1
       grind)
    | exact resolve eq1107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq18863 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18687 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq18687
    | (have j0 := eq18687 X0 X1
       grind)
    | exact resolve eq18687 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18687
  have eq27388 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 (M.op X1 X1)) X0
       have i₂ := eq2806 X1 X0
       grind)
    | exact superpose eq2806 eq1030
    | (have j1 := eq2806 X1 X0
       grind)
    | exact resolve eq1030 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq27507 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27388 X0 X1
       have i₂ := eq5267 (M.op X1 X1) X1
       grind)
    | exact superpose eq5267 eq27388
    | (have j0 := eq27388 X0 X1
       grind)
    | exact resolve eq27388 eq5267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5267 eq27388
  have eq27666 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27507 X0 X1
       have i₂ := eq91 (M.op X1 X1)
       grind)
    | exact superpose eq91 eq27507
    | (have j0 := eq27507 X0 X1
       grind)
    | exact resolve eq27507 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27507
  have eq27714 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27666 X0 X1
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq27666
    | (have j0 := eq27666 X0 X1
       grind)
    | exact resolve eq27666 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27666
  have eq28513 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X1) X2)) (M.op X2 (M.op X0 X0))) = X3 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1203 X1 X2 X3
       have i₂ := eq27714 X3 X0
       grind)
    | (have i₁ := eq1203 X0 X1 X1
       have i₂ := eq27714 X0 X1
       grind)
    | exact superpose eq27714 eq1203
    | (have j1 := eq27714 X3 X0
       grind)
    | exact resolve eq1203 eq27714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27714
  have eq28864 : ∀ X0 X3 : G, (M.op X0 X3) = (k X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq28513 X0 x x X3
       have i₂ := eq1203 x x X0
       grind)
    | exact superpose eq1203 eq28513
    | (have j0 := eq28513 X0 x x X3
       grind)
    | exact resolve eq28513 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq28513
  have eq29351 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28864 (σ X0) (σ X1)
       grind)
    | exact superpose eq28864 eq13
    | (have j1 := eq28864 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29374 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12632
       have i₂ := eq28864 x y
       grind)
    | exact superpose eq28864 eq12632
    | (have j1 := eq28864 x (M.op x y)
       grind)
    | exact resolve eq12632 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28864
  have eq30188 : (M.op y (M.op y y)) = (M.op (M.op x (M.op x x)) x) ∨ x = y := by
    first
    | (have i₁ := eq1030 y x
       have i₂ := eq29374
       grind)
    | exact superpose eq29374 eq1030
    | exact resolve eq1030 eq29374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq29374
  have eq30203 : (M.op x x) = (M.op y (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq30188
       have i₂ := eq770 x
       grind)
    | exact superpose eq770 eq30188
    | exact resolve eq30188 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq30188
  have eq31434 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq978
    | exact resolve eq978 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq31491 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31434 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31434
    | (have j0 := eq31434 X0 X1
       grind)
    | exact resolve eq31434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31434
  have eq31495 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31491 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31491
    | (have j0 := eq31491 X0 X1
       grind)
    | exact resolve eq31491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31491
  have eq31497 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31495 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31495
    | (have j0 := eq31495 X0 X1
       grind)
    | exact resolve eq31495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31498 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31497 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31497
    | (have j0 := eq31497 X0 X1
       grind)
    | exact resolve eq31497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31497
  have eq36486 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31498 x (M.op (M.op x x) (M.op X0 (M.op X0 X0)))
       have i₂ := eq727 X0 x
       grind)
    | exact superpose eq727 eq31498
    | (have j1 := eq727 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq31498 x (M.op (M.op x x) (M.op x (M.op x x)))
       have r₂ := eq727 x x
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (M.op X0 X0) (k X0 X1)
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (k X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq31498 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq36493 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31498 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq758 X0
       grind)
    | exact superpose eq758 eq31498
    | (have j1 := eq758 X0
       grind)
    | exact resolve eq31498 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq36522 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31498 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq31498
    | exact resolve eq31498 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq31498
  have eq36530 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36493
  have eq36548 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36530 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36530
    | (have j0 := eq36530 X0
       grind)
    | exact resolve eq36530 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36530
  have eq37379 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36548 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq36548
    | (have j0 := eq36548 X1
       grind)
    | exact resolve eq36548 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq36548
  have eq39748 : y = (k y (M.op (M.op y y) (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq30203
       grind)
    | exact superpose eq30203 eq104
    | exact resolve eq104 eq30203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq30203
  have eq39861 : y = (k y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have j1 := eq105 x y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 y (k y (M.op (M.op y y) (M.op x x)))
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 (k y (M.op (M.op y y) (M.op x x))) y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 x y
       grind)
    | exact resolve eq39748 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq39748
  have eq40235 : (σ y) = (σ (M.op y (M.op (M.op y y) (M.op x x)))) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq1384 (M.op (M.op y y) (M.op x x)) y
       have i₂ := eq39861
       grind)
    | exact superpose eq39861 eq1384
    | (have j0 := eq1384 (M.op (M.op y y) (M.op x x)) y
       grind)
    | exact resolve eq1384 eq39861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq39861
  have eq40244 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq40235
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40235
    | exact resolve eq40235 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40235
  have eq40277 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40244
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40244
    | exact resolve eq40244 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40244
  have eq41585 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1419 y
       have i₂ := eq40277
       grind)
    | exact superpose eq40277 eq1419
    | exact resolve eq1419 eq40277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq40277
  have eq272295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29351 x y
       grind)
    | exact superpose eq29351 eq14
    | (have j1 := eq29351 x y
       grind)
    | exact resolve eq14 eq29351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29351
  have eq272304 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272295
       have i₂ := eq12632
       grind)
    | exact superpose eq12632 eq272295
    | exact resolve eq272295 eq12632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12632 eq272295
  have eq272308 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272304
       have i₂ := eq41585
       grind)
    | exact superpose eq41585 eq272304
    | exact resolve eq272304 eq41585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41585 eq272304
  have eq272320 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq272308
  have eq272321 : (σ x) = (σ y) := by grind
  clear eq272320
  have eq272325 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq272321
       grind)
    | exact superpose eq272321 eq9
    | exact resolve eq9 eq272321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272321
  have eq272399 : x = y := by
    first
    | (have i₁ := eq272325
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq272325
    | exact resolve eq272325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272325
  have eq272403 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq272399
       grind)
    | exact superpose eq272399 eq14
    | exact resolve eq14 eq272399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272399
  have eq304788 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36522 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq18863 X0 X1
       grind)
    | exact superpose eq18863 eq36522
    | (have j1 := eq18863 X1 X0
       grind)
    | (have r₁ := eq36522 X0 X1
       have r₂ := eq18863 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq36522 eq18863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18863 eq36522
  have eq313420 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X1 X1) = (σ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq304788 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq304788
    | (have j0 := eq304788 (σ X0) X1
       grind)
    | (have r₁ := eq304788 (σ (M.op (τ X1) (τ X1))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq304788 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304788
  have eq313423 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313420 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq313420
    | (have j0 := eq313420 X1 (σ X0)
       grind)
    | (have r₁ := eq313420 (τ (σ (M.op (τ X1) (τ X1)))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq313420 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313420
  have eq313430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq313423 (M.op (σ X0) (σ X0)) (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313423
  have eq313443 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq313430 x
       grind)
    | exact superpose eq313430 eq272403
    | (have j1 := eq313430 x
       grind)
    | (have r₁ := eq272403
       have r₂ := eq313430 x
       grind)
    | exact resolve eq272403 eq313430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313430
  have eq313453 : x = (M.op x x) := by grind
  clear eq313443
  have eq313839 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op x (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1 x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1172
    | exact resolve eq1172 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq313855 : ∀ X0 : G, (k X0 (τ (M.op x (M.op x (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1218 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1218
    | exact resolve eq1218 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq313907 : ∀ X0 : G, x ≠ (k (M.op x x) X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq3544 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq3544
    | exact resolve eq3544 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq314012 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq36486 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq36486
    | (have j0 := eq36486 x X0
       grind)
    | exact resolve eq36486 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486
  have eq314017 : ∀ X0 : G, (M.op x (M.op x X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37379 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq37379
    | (have j0 := eq37379 X0 X0
       grind)
    | exact resolve eq37379 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37379
  have eq314204 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq314012 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314012
  have eq314287 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq313907 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq313907
    | (have j0 := eq313907 X0
       grind)
    | exact resolve eq313907 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313907
  have eq314392 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq314287 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq314287
    | (have j0 := eq314287 X0
       grind)
    | exact resolve eq314287 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314287
  have eq314443 : ∀ X0 X1 X2 : G, x ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314204 X2
       have i₂ := eq1196 X1 X2 X0
       grind)
    | exact superpose eq1196 eq314204
    | (have j0 := eq314204 X2
       grind)
    | exact resolve eq314204 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq314204
  have eq314526 : ∀ X1 X2 : G, x ≠ (M.op x (M.op x (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq314443 x X1 X2
       have i₂ := eq313839 x (M.op X1 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq313839 eq314443
    | (have j0 := eq314443 x X1 X2
       grind)
    | exact resolve eq314443 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314443
  have eq314529 : ∀ X2 : G, x ≠ (M.op x (M.op x (M.op x (M.op x X2)))) ∨ x = X2 := by
    intro X2
    first
    | (have i₁ := eq314526 x X2
       have i₂ := eq313839 x X2
       grind)
    | exact superpose eq313839 eq314526
    | (have j0 := eq314526 x X2
       grind)
    | exact resolve eq314526 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313839 eq314526
  have eq315721 : x ≠ x ∨ x = (M.op x (τ (M.op x (M.op x (σ x))))) := by
    first
    | (have i₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq313855 x
       grind)
    | exact superpose eq313855 eq314392
    | (have j0 := eq314392 (τ (M.op x (M.op x (σ x))))
       grind)
    | (have r₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have r₂ := eq313855 x
       grind)
    | exact resolve eq314392 eq313855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313855 eq314392
  have eq315727 : x = (M.op x (τ (M.op x (M.op x (σ x))))) := by grind
  clear eq315721
  have eq321271 : x ≠ (M.op x (M.op x (M.op x x))) ∨ x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have i₁ := eq314529 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq315727
       grind)
    | exact superpose eq315727 eq314529
    | (have j0 := eq314529 (τ (M.op x (M.op x (σ x))))
       grind)
    | exact resolve eq314529 eq315727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314529 eq315727
  have eq321319 : x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have r₁ := eq321271
       have r₂ := eq91 x
       grind)
    | exact resolve eq321271 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq321271
  have eq321333 : (σ x) = (M.op x (M.op x (σ x))) := by
    first
    | (have i₁ := eq10 (M.op x (M.op x (σ x)))
       have i₂ := eq321319
       grind)
    | exact superpose eq321319 eq10
    | exact resolve eq10 eq321319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321319
  have eq321487 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq314017 (σ x)
       have i₂ := eq321333
       grind)
    | exact superpose eq321333 eq314017
    | (have j0 := eq314017 (σ x)
       grind)
    | (have r₁ := eq314017 (σ x)
       have r₂ := eq321333
       grind)
    | exact resolve eq314017 eq321333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314017 eq321333
  have eq321534 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq321487
  have eq321597 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq321534
       grind)
    | exact superpose eq321534 eq272403
    | exact resolve eq272403 eq321534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272403 eq321534
  have eq322149 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq321597
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq321597
    | exact resolve eq321597 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313453 eq321597
  have eq322150 : False := by grind
  exact eq322150

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq118 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq122 (σ X0) (σ X1)
       grind)
    | exact superpose eq122 eq13
    | exact resolve eq13 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq138
    | exact resolve eq138 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq138
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq14
    | (have r₁ := eq14
       have r₂ := eq145 x y
       grind)
    | exact resolve eq14 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1283 : False := by grind
  exact eq1283
