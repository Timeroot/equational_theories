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

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation887 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (M.op X0 X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X1
       have i₂ := eq22 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq38 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1) X1
       have i₂ := eq26 (M.op X1 X1) X1
       grind)
    | exact superpose eq26 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq26 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) X1
       have i₂ := eq26 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq63 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq55 X0 (τ X1)
       grind)
    | exact superpose eq55 eq16
    | exact resolve eq16 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq297 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq305 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq55 X0 (σ X1)
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55
  have eq324 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x x
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq22
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq22 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41
  have eq393 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 (M.op X1 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq106
    | (have j0 := eq106 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq106 X0 (M.op X1 X1)
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq398 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq418 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X1 X1)
       have i₂ := eq398 (σ X0) X1
       grind)
    | exact superpose eq398 eq63
    | exact resolve eq63 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq421 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq418
    | exact resolve eq418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq2209 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq324
       have i₂ := eq43 x X0 y
       grind)
    | exact superpose eq43 eq324
    | (have j1 := eq43 x X0 x
       grind)
    | exact resolve eq324 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq324
  have eq2213 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq2209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2890 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq328 (τ X0) (τ X1)
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq328
    | (have j0 := eq328 (τ X0) X1
       grind)
    | exact resolve eq328 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq328
  have eq2992 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2890 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2890
    | (have j0 := eq2890 X0 X1
       grind)
    | exact resolve eq2890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3003 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2992 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2992
    | (have j0 := eq2992 X0 X1
       grind)
    | exact resolve eq2992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3005 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3003
    | (have j0 := eq3003 X0 X1
       grind)
    | exact resolve eq3003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3006 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3005 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3005
    | (have j0 := eq3005 X0 X1
       grind)
    | exact resolve eq3005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3348 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X2 (k X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq3006 X0 X2
       grind)
    | exact superpose eq3006 eq54
    | (have j1 := eq3006 X0 X2
       grind)
    | exact resolve eq54 eq3006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 (k X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq398 X1 X0
       have i₂ := eq3006 X0 X2
       grind)
    | exact superpose eq3006 eq398
    | (have j1 := eq3006 X0 X2
       grind)
    | exact resolve eq398 eq3006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq3006
  have eq4441 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq3348 X0 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq4443 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4441 X0
       have j1 := eq3355 X0 x X0
       grind)
    | (have r₁ := eq4441 X0
       have r₂ := eq3355 X0 X0 x
       grind)
    | exact resolve eq4441 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq4441
  have eq4630 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 (k X0 X0) X1 X2
       have i₂ := eq4443 X0
       grind)
    | exact superpose eq4443 eq21
    | exact resolve eq21 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k X0 X0)
       have i₂ := eq4443 X0
       grind)
    | exact superpose eq4443 eq24
    | exact resolve eq24 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4663 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4630 X0 X1 x
       have i₂ := eq27 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq27 eq4630
    | exact resolve eq4630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4630
  have eq5898 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X1 (σ (M.op X1 X1))
       have i₂ := eq4663 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq4663 eq237
    | exact resolve eq237 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq5903 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X1 (τ (M.op X1 X1))
       have i₂ := eq4663 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq4663 eq305
    | exact resolve eq305 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq4663
  have eq7818 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5903 x X2
       have i₂ := eq5903 x X0
       grind)
    | exact superpose eq5903 eq5903
    | exact resolve eq5903 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7897 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5898 x X2
       have i₂ := eq5903 x X0
       grind)
    | exact superpose eq5903 eq5898
    | exact resolve eq5898 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq7902 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X1
       have i₂ := eq5903 X1 X0
       grind)
    | exact superpose eq5903 eq24
    | exact resolve eq24 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq11289 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7902 (τ (M.op X0 X0)) X1
       have i₂ := eq7902 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq7902 eq7902
    | exact resolve eq7902 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902
  have eq13835 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 (σ x)
       have i₂ := eq2213 X1
       grind)
    | exact superpose eq2213 eq421
    | (have j1 := eq2213 X1
       grind)
    | exact resolve eq421 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq2213
  have eq13960 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13835 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13835
    | (have j0 := eq13835 X0 X1
       grind)
    | exact resolve eq13835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq19255 : x ≠ x ∨ x = (k x x) := by
    first
    | (have j0 := eq13960 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13960
  have eq19256 : x = (k x x) := by grind
  clear eq19255
  have eq19262 : x = (M.op x x) := by
    first
    | (have i₁ := eq19256
       have i₂ := eq4632 x
       grind)
    | exact superpose eq4632 eq19256
    | exact resolve eq19256 eq4632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4632 eq19256
  have eq19553 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq26
    | exact resolve eq26 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19556 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq32 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq32
    | exact resolve eq32 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19557 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 x X0
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq54
    | exact resolve eq54 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq19575 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq5903 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq5903
    | exact resolve eq5903 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5903
  have eq19585 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq7818 x X0
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq7818
    | exact resolve eq7818 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7818 eq19262
  have eq20045 : ∀ X0 : G, x = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11289 X0 x
       have i₂ := eq19553 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq19553 eq11289
    | exact resolve eq11289 eq19553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289 eq19553
  have eq20048 : x = (τ (τ x)) := by
    first
    | (have i₁ := eq20045 x
       have i₂ := eq19585 x
       grind)
    | exact superpose eq19585 eq20045
    | exact resolve eq20045 eq19585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19585 eq20045
  have eq20565 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7897 X0 x
       have i₂ := eq19556 x
       grind)
    | exact superpose eq19556 eq7897
    | exact resolve eq7897 eq19556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7897 eq19556
  have eq20710 : (σ x) = (τ (τ x)) := by
    first
    | (have i₁ := eq20565 x
       have i₂ := eq19575 x
       grind)
    | exact superpose eq19575 eq20565
    | exact resolve eq20565 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19575 eq20565
  have eq20749 : x = (σ x) := by
    first
    | (have i₁ := eq20710
       have i₂ := eq20048
       grind)
    | exact superpose eq20048 eq20710
    | exact resolve eq20710 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq20710
  have eq21167 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20749
       grind)
    | exact superpose eq20749 eq14
    | exact resolve eq14 eq20749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20749
  have eq21234 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq21167
       have i₂ := eq19557 (σ y)
       grind)
    | exact superpose eq19557 eq21167
    | exact resolve eq21167 eq19557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21167
  have eq21253 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21234
       have i₂ := eq19557 y
       grind)
    | exact superpose eq19557 eq21234
    | exact resolve eq21234 eq19557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19557 eq21234
  have eq21254 : False := by grind
  exact eq21254

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

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation895 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law895 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law895.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X3) (M.op X2 X3))))) = X2 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq78
    | (have j0 := eq78 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq78 X1 (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq78 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq91 X1 (M.op X0 X1)
       grind)
    | exact superpose eq91 eq8
    | exact resolve eq8 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq144 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X1 (M.op X0 X1)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq107
    | exact resolve eq107 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq202 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq109 (σ X0) X1
       grind)
    | exact superpose eq109 eq28
    | exact resolve eq28 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq109
  have eq208 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq202
    | exact resolve eq202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq264 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq144
    | exact resolve eq144 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq144
  have eq444 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1227 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq108 X0 (σ X1)
       grind)
    | exact superpose eq108 eq20
    | exact resolve eq20 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq108
  have eq2485 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq480 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq480
    | (have j0 := eq480 (τ X0)
       grind)
    | exact resolve eq480 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq480
  have eq2496 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2485 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2485
    | (have j0 := eq2485 X0
       grind)
    | exact resolve eq2485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2505 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2496 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2496
    | (have j0 := eq2496 X0
       grind)
    | exact resolve eq2496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq6147 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq444
       have i₂ := eq48 x X0 y
       grind)
    | exact superpose eq48 eq444
    | (have j1 := eq48 x X0 x
       grind)
    | exact resolve eq444 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq444
  have eq6154 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq6147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq170059 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 (σ x) X1
       have i₂ := eq6154 X0
       grind)
    | exact superpose eq6154 eq1227
    | (have j1 := eq6154 X1
       grind)
    | exact resolve eq1227 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq6154
  have eq170369 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq170059 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq170059
    | (have j0 := eq170059 X0 X0
       grind)
    | exact resolve eq170059 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170059
  have eq175942 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq170369 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170369
  have eq175943 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq175942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175942
  have eq185729 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2505 x
       have i₂ := eq175943 x
       grind)
    | exact superpose eq175943 eq2505
    | (have j0 := eq2505 x
       grind)
    | (have r₁ := eq2505 x
       have r₂ := eq175943 x
       grind)
    | exact resolve eq2505 eq175943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175943
  have eq185777 : x = (M.op x x) := by grind
  clear eq185729
  have eq186056 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq145 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq145
    | exact resolve eq145 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq186058 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq208 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq208
    | exact resolve eq208 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq186060 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq264 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq264
    | exact resolve eq264 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq185777
  have eq199913 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq2505 (τ x)
       have i₂ := eq186058 (τ x)
       grind)
    | exact superpose eq186058 eq2505
    | (have j0 := eq2505 (τ x)
       grind)
    | (have r₁ := eq2505 (τ x)
       have r₂ := eq186058 (τ x)
       grind)
    | exact resolve eq2505 eq186058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq186058
  have eq199966 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq199913
  have eq200008 : x = (τ x) := by
    first
    | (have i₁ := eq199966
       have i₂ := eq186060 (τ x)
       grind)
    | exact superpose eq186060 eq199966
    | exact resolve eq199966 eq186060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186060 eq199966
  have eq201638 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq200008
       grind)
    | exact superpose eq200008 eq10
    | exact resolve eq10 eq200008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200008
  have eq202369 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq201638
       grind)
    | exact superpose eq201638 eq14
    | exact resolve eq14 eq201638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201638
  have eq202439 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq202369
       have i₂ := eq186056 (σ y)
       grind)
    | exact superpose eq186056 eq202369
    | exact resolve eq202369 eq186056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202369
  have eq202463 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq202439
       have i₂ := eq186056 y
       grind)
    | exact superpose eq186056 eq202439
    | exact resolve eq202439 eq186056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186056 eq202439
  have eq202464 : False := by grind
  exact eq202464

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
